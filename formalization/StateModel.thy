theory StateModel
  imports Syntax "HOL-Library.Monad_Syntax"
begin

section "Result Monad"

subsection "Type"

datatype error = unknown_register_name | invalid_address | global_register_overwrite
  | not_an_address | incompatible_types | unknown_label
  | phi_no_previous_block | phi_label_not_found | phi_label_not_distinct
  | internal_error | unfreeable_memory | invalid_parameter_length | no_return_value

datatype 'a result = ok 'a | err error


subsection "Monadic Operations"

definition bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind R f = (case R of err e \<Rightarrow> err e | ok x \<Rightarrow> f x)"

definition return :: "'a \<Rightarrow> 'a result" where
  "return x = ok x"

adhoc_overloading
  Monad_Syntax.bind==bind

fun assert where "assert e True = ok ()" | "assert e False = err e"


subsection "Lemmas"


context
  notes bind_def[simp] return_def[simp]
begin


(* Monad laws *)

lemma result_monad_left_identity[simp]: "do {x'\<leftarrow>return x; f x'} = f x"
  by auto

lemma result_monad_right_identity[simp]: "do {x \<leftarrow> m; return x} = m"
  by (cases m; simp)

lemma result_monad_associative[simp]: "do {y \<leftarrow> do {x \<leftarrow> (m::'a result); f x}; g y} = do {x \<leftarrow> m; do {y \<leftarrow> f x; g y}}"
  by (cases m; simp)


(* Simps *)

lemma assert_ok_iff[simp]: "assert e P = ok x \<longleftrightarrow> P"
  by (cases P; simp)

lemma assert_err_iff[simp]: "assert e P = err e' \<longleftrightarrow> \<not>P \<and> e'=e"
  by (cases P; auto)


lemma result_bind_ok_iff[simp]: "do { x\<leftarrow>m; f x } = ok v \<longleftrightarrow> (\<exists>x. m = ok x \<and> f x = ok v)"
  by (cases m; simp)

lemma result_bind_ok_unit[simp]: "do {ok (); f y} = do {f y}"
  by simp

lemma result_bind_err_iff[simp]: "do { x\<leftarrow>m; f x } = err e \<longleftrightarrow> (m = err e \<or> (\<exists>x. m = ok x \<and> f x = err e))"
  by (cases m; simp)

lemma result_return_ok_iff[simp]: "return x = ok y \<longleftrightarrow> x = y"
  by simp

lemma result_err_propagate[simp]: "do {x \<leftarrow> err e; f x} = err e"
  by auto

lemma result_let_in[simp]: "do { z \<leftarrow> (let x = y in (f x :: 'a result)); g z} = (let x = y in (do {z \<leftarrow> f x; g z }))"
  by simp

end


section "Execution State"

type_synonym llvm_register_model = "(string, llvm_value) mapping"
type_synonym llvm_global_variable_model = "(string, memory_model_address) mapping"


datatype memory_value = mem_unset | mem_val llvm_value | mem_freed
type_synonym llvm_memory_model = "memory_value list"

definition empty_memory :: "llvm_memory_model" where
  "empty_memory = []"


type_synonym state = "llvm_register_model * llvm_global_variable_model * llvm_memory_model * llvm_memory_model * llvm_memory_model"

definition empty_state :: "state" where
  "empty_state = (Mapping.empty, Mapping.empty, empty_memory, empty_memory, empty_memory)"


section "Basic State Operations"

subsection "Register operations"

(* Get *)
fun get_local_register :: "llvm_register_model \<Rightarrow> string \<Rightarrow> llvm_value result" where
  "get_local_register r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register_name | Some v \<Rightarrow> ok v)"

fun get_global_var :: "llvm_global_variable_model \<Rightarrow> string \<Rightarrow> llvm_value result" where
  "get_global_var r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register_name | Some v \<Rightarrow> ok (addr (gaddr v)))"

fun get_register :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_register _ (val v) = ok v"
| "get_register (lr,gr,sm,hm,gm) (reg (lid n)) = get_local_register lr n"
| "get_register (lr,gr,sm,hm,gm) (reg (gid n)) = get_global_var gr n"


(* Set *)
definition set_single_register :: "string \<Rightarrow> llvm_value \<Rightarrow> llvm_register_model \<Rightarrow> llvm_register_model" where
  "set_single_register n v r = Mapping.update n v r"

fun set_register :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> state result" where
  "set_register (lid n) v (lr,gr,sm,hm,gm) = ok (set_single_register n v lr,gr,sm,hm,gm)"
| "set_register _ _ _ = err global_register_overwrite"


subsection "Memory operations"

(* Allocate *)
definition allocate_single_memory :: "llvm_memory_model \<Rightarrow> (llvm_memory_model * memory_model_address)" where
  "allocate_single_memory m = (m@[mem_unset], length m)"

definition allocate_stack :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_stack s = (case s of (lr,gr,sm,hm,gm) \<Rightarrow> let (m, a) = allocate_single_memory sm in ((lr,gr,m,hm,gm), saddr a))"

definition allocate_heap :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_heap s = (case s of (lr,gr,sm,hm,gm) \<Rightarrow> let (m, a) = allocate_single_memory hm in ((lr,gr,sm,m,gm), haddr a))"

definition allocate_global :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_global s = (case s of (lr,gr,sm,hm,gm) \<Rightarrow> let (m, a) = allocate_single_memory gm in ((lr,gr,sm,hm,m), gaddr a))"


(* Address validity *)
definition allocated_single_memory_address :: "llvm_memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "allocated_single_memory_address m a = (a < length m)"
definition valid_single_memory_address :: "llvm_memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_single_memory_address m a = (allocated_single_memory_address m a \<and> m!a \<noteq> mem_freed)"

fun allocated_memory_address :: "state \<Rightarrow> llvm_address \<Rightarrow> bool" where
  "allocated_memory_address (lr,gr,sm,hm,gm) (haddr a) = allocated_single_memory_address hm a"
| "allocated_memory_address (lr,gr,sm,hm,gm) (saddr a) = allocated_single_memory_address sm a"
| "allocated_memory_address (lr,gr,sm,hm,gm) (gaddr a) = allocated_single_memory_address gm a"

fun valid_memory_address :: "state \<Rightarrow> llvm_address \<Rightarrow> bool" where
  "valid_memory_address (lr,gr,sm,hm,gm) (haddr a) = valid_single_memory_address hm a"
| "valid_memory_address (lr,gr,sm,hm,gm) (saddr a) = valid_single_memory_address sm a"
| "valid_memory_address (lr,gr,sm,hm,gm) (gaddr a) = valid_single_memory_address gm a"


(* Get *)
definition get_single_memory :: "llvm_memory_model \<Rightarrow> memory_model_address \<Rightarrow> llvm_value result" where
  "get_single_memory m a = do {
    assert invalid_address (allocated_single_memory_address m a);
    (case (m!a) of
      mem_unset \<Rightarrow> err invalid_address
    | mem_val v \<Rightarrow> ok v
    | mem_freed \<Rightarrow> err invalid_address)
  }"

fun get_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "get_memory (lr,gr,sm,hm,gm) (haddr a) = get_single_memory hm a"
| "get_memory (lr,gr,sm,hm,gm) (saddr a) = get_single_memory sm a"
| "get_memory (lr,gr,sm,hm,gm) (gaddr a) = get_single_memory gm a"


(* Set *)
definition set_single_memory :: "memory_model_address \<Rightarrow> llvm_value \<Rightarrow> llvm_memory_model \<Rightarrow> llvm_memory_model result" where
  "set_single_memory a v m = do {
    assert invalid_address (valid_single_memory_address m a);
    return (m[a:=(mem_val v)])
  }"

fun set_memory :: "llvm_address \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> state result" where
  "set_memory (saddr a) v (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> set_single_memory a v sm;
    return (lr,gr,m,hm,gm)
  }"
| "set_memory (haddr a) v (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> set_single_memory a v hm;
    return (lr,gr,sm,m,gm)
  }"
| "set_memory (gaddr a) v (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> set_single_memory a v gm;
    return (lr,gr,sm,hm,m)
  }"


(* Free *)
definition free_single_memory :: "memory_model_address \<Rightarrow> llvm_memory_model \<Rightarrow> llvm_memory_model result" where
  "free_single_memory a m = do {
    assert invalid_address (valid_single_memory_address m a);
    return (m[a:=mem_freed])
  }"

fun free_memory :: "llvm_address \<Rightarrow> state \<Rightarrow> state result" where
  "free_memory (haddr a) (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> free_single_memory a hm;
    return (lr,gr,sm,m,gm)
  }"
| "free_memory _ _ = err unfreeable_memory"



subsection "Stack Frames"

fun push_frame :: "state \<Rightarrow> state" where "push_frame (lr,gr,sm,hm,gm) = (Mapping.empty,gr,sm,hm,gm)"
fun pop_frame :: "state \<Rightarrow> state \<Rightarrow> state" where "pop_frame (lr,gr,sm,hm,gm) (lr',gr',sm',hm',gm') = (lr,gr',take (length sm) sm',hm',gm')"



section "Abstractions"


subsection "Memory"

definition single_memory_\<alpha> where
  "single_memory_\<alpha> m a \<equiv> if allocated_single_memory_address m a
  then Some (m!a)
  else None"

fun memory_\<alpha> :: "state \<Rightarrow> llvm_address \<Rightarrow> memory_value option" where
  "memory_\<alpha> (lr,gr,sm,hm,gm) (saddr a) = single_memory_\<alpha> sm a"
| "memory_\<alpha> (lr,gr,sm,hm,gm) (haddr a) = single_memory_\<alpha> hm a"
| "memory_\<alpha> (lr,gr,sm,hm,gm) (gaddr a) = single_memory_\<alpha> gm a"


subsection "Register"

fun register_\<alpha> :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "register_\<alpha> (lr,gr,sm,hm,gm) (val v) = Some v"
| "register_\<alpha> (lr,gr,sm,hm,gm) (reg (lid n)) = Mapping.lookup lr n"
| "register_\<alpha> (lr,gr,sm,hm,gm) (reg (gid n)) = (case Mapping.lookup gr n of Some a \<Rightarrow> Some (addr (gaddr a)) | None \<Rightarrow> None)"


subsection "Properties"


lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (lr,gr,sm,hm,gm) = memory_\<alpha> (lr',gr',sm,hm,gm)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma register_\<alpha>_lid_update_eq[simp]:
  "register_\<alpha> (Mapping.update n v lr,gr,sm,hm,gm) = (register_\<alpha> (lr,gr,sm,hm,gm))(reg (lid n) := Some v)"
  apply (auto simp: fun_eq_iff split: llvm_value_ref.split)
  subgoal for x apply (cases x; simp) subgoal for id by (cases id; simp)
  done
  done

lemma register_\<alpha>_val_eq[simp]:
  "register_\<alpha> s (val v) = Some v"
  by (cases s; simp)

lemma register_\<alpha>_update_independent[simp]:
  "(register_\<alpha> s)(x := v) = register_\<alpha> s' \<Longrightarrow> x \<noteq> y \<Longrightarrow> register_\<alpha> s y = register_\<alpha> s' y"
  by (metis fun_upd_other)

lemma register_\<alpha>_eq_get_register:
  "register_\<alpha> s v = Some v' \<longleftrightarrow> get_register s v = ok v'"
  apply (cases s; cases v; auto)
  subgoal for _ _ _ _ _ n by (cases n; simp split: option.splits)
  subgoal for _ _ _ _ _ n by (cases n; simp split: option.splits)
  done

lemma set_register_\<alpha>:
  "set_register n v s = ok s' \<Longrightarrow> register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v)"
  apply (cases s; rule ext)
  subgoal for l' g' s' h' x by (cases x; cases n; auto simp: set_single_register_def)
  done


lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>n. register_\<alpha> s''' (reg (lid n)) = register_\<alpha> s (reg (lid n))"
  by (cases s; cases s'; cases s''; cases s'''; fastforce)

lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>n. register_\<alpha> s''' (reg (gid n)) = register_\<alpha> s'' (reg (gid n))"
  by (cases s; cases s'; cases s''; cases s'''; fastforce)



end
