theory Steps
  imports Instructions
begin

context fixes program :: "llvm_program"
begin

section "Step Relation"

datatype instruction_state = 
    execi "llvm_identifier option" llvm_instruction_block state
  | flowi state llvm_block_return
  | is_erri: erri

datatype (discs_sels) function_state = 
    branchf (state: state) "llvm_identifier option" llvm_identifier llvm_identifier
  | retf (state: state) (ret_value: "llvm_value option") (ret_func: llvm_identifier)
  | is_errf: errf

definition "first_label f \<equiv> (case llvm_function.blocks f of ((l,b)#fs) \<Rightarrow> Some l | _ \<Rightarrow> None)"

fun assign_params :: "(llvm_identifier * llvm_type) list \<Rightarrow> (llvm_type * llvm_value_ref) list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> state result" where
  "assign_params [] [] s s' = ok s'"
| "assign_params [] _ s s' = err invalid_parameter_length"
| "assign_params _ [] s s' = err invalid_parameter_length"
| "assign_params ((n,t)#ps) ((t',v)#vs) s s' = do {
    val \<leftarrow> dereference s v;
    s'' \<leftarrow> set_register n val s';
    assign_params ps vs s s''
  }"
fun prepare_state :: "state \<Rightarrow> (llvm_identifier * llvm_type) list \<Rightarrow> (llvm_type * llvm_value_ref) list \<Rightarrow> state result" where
  "prepare_state s ps vs = assign_params ps vs s (push_frame s)"
fun restore_state :: "state \<Rightarrow> state \<Rightarrow> llvm_value option \<Rightarrow> llvm_identifier option \<Rightarrow> state result" where
  "restore_state s s' None None = ok (pop_frame s s')"
| "restore_state s s' (Some v) (Some n) = set_register n v (pop_frame s s')"
| "restore_state s s' (Some _) None = ok (pop_frame s s')"
| "restore_state _ _ _ _ = err no_return_value"

lemma wp_assign_params_intro:
  assumes "register_\<alpha> s v = Some va" 
  assumes "\<And>s''. register_\<alpha> s'' = (register_\<alpha> s')(reg n := Some va) \<Longrightarrow> memory_\<alpha> s'' = memory_\<alpha> s' \<Longrightarrow> wp (assign_params ps vs s s'') Q"
  assumes "is_lid n"
  shows "wp (assign_params ((n,t)#ps) ((t',v)#vs) s s') Q"
  apply simp apply (intro wp_intro) using assms by auto

lemma wp_assign_params_empty_intro:
  assumes "Q s'"
  shows "wp (assign_params [] [] s s') Q"
  using assms by simp

lemma wp_restore_state_intro:
  assumes "\<And>n. rn = Some n \<Longrightarrow> rv = Some v"
  assumes "\<And>n. rn = Some n \<Longrightarrow> wp (set_register n v (pop_frame s s')) Q"
  assumes "rn = None   \<Longrightarrow> Q (pop_frame s s')"
  shows "wp (restore_state s s' rv rn) Q"
  using assms
  unfolding wp_def
  by (cases rn; cases rv; simp)

inductive
  step_i :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>i" 50)
and
  step_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f" 50)
where
(* Control flow *)
"(execi pre ([],[],br_label l) s) \<rightarrow>\<^sub>i (flowi s (branch_label l))"

| "dereference s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. dereference s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i erri"

| "(execi pre ([],[],ret None) s) \<rightarrow>\<^sub>i (flowi s (return_value None))"

| "dereference s v = ok v' \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i (flowi s (return_value (Some v')))"
| "dereference s v = err _ \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i erri"

(* Function calls *)
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> step_f\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)
  \<Longrightarrow> restore_state s s'' v' n = ok s'''
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i (execi pre ([],is,t) s''')"
| "map_of program f = None
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = None
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = err _
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> step_f\<^sup>*\<^sup>* (branchf s' None b f) errf
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> step_f\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)
  \<Longrightarrow> restore_state s s'' v' n = err _
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"

(* Normal instructions *)
| "execute_instruction i s = ok s'
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> (execi pre ([],i#is,t) s) \<rightarrow>\<^sub>i (execi pre ([],is,t) s')"
| "execute_instruction i s = err _
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> (execi pre ([],i#is,t) s) \<rightarrow>\<^sub>i erri"

(* Phi nodes *)
| "execute_phi pre p s = ok s' \<Longrightarrow>
    (execi pre (p#ps,is,t) s) \<rightarrow>\<^sub>i (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    (execi pre (p#ps,is,t) s) \<rightarrow>\<^sub>i erri"

(* Blocks *)
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i\<^sup>*\<^sup>* (execi prev b s) (flowi s' (branch_label l)) \<Longrightarrow>                                                          
    branchf s prev lab f \<rightarrow>\<^sub>f branchf s' (Some lab) l f"
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i\<^sup>*\<^sup>* (execi prev b s) (flowi s' (return_value v)) \<Longrightarrow>
    branchf s prev lab f \<rightarrow>\<^sub>f retf s' v f"

(* Block errors *)
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i\<^sup>*\<^sup>* (execi prev b s) erri \<Longrightarrow>
    branchf s prev lab f \<rightarrow>\<^sub>f errf"
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = None \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f errf"
| "map_of program f = None \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f errf"


abbreviation steps_i (infix "\<rightarrow>\<^sub>i*" 50) where
  "s \<rightarrow>\<^sub>i* s' \<equiv> step_i\<^sup>*\<^sup>* s s'"
abbreviation steps_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f*" 50) where
  "s \<rightarrow>\<^sub>f* s' \<equiv> step_f\<^sup>*\<^sup>* s s'"


section "Terminal States"

definition terminal_i where
  "terminal_i s \<equiv> (case s of flowi _ _ \<Rightarrow> True | erri \<Rightarrow> True | _ \<Rightarrow> False)"
definition terminal_f where
  "terminal_f s \<equiv> (case s of retf _ _ _ \<Rightarrow> True | errf \<Rightarrow> True | _ \<Rightarrow> False)"

notation terminal_i ("_ \<nexists>\<rightarrow>\<^sub>i" 50)
notation terminal_f ("_ \<nexists>\<rightarrow>\<^sub>f" 50)

abbreviation terminates_to_i where
  "terminates_to_i s s' \<equiv> s \<rightarrow>\<^sub>i* s' \<and> (s' \<nexists>\<rightarrow>\<^sub>i)"
abbreviation terminates_to_f where
  "terminates_to_f s s' \<equiv> s \<rightarrow>\<^sub>f* s' \<and> (s' \<nexists>\<rightarrow>\<^sub>f)"

lemma terminal_state_simps[simp]:
  "flowi s br \<nexists>\<rightarrow>\<^sub>i"
  "erri \<nexists>\<rightarrow>\<^sub>i"
  "\<not>(execi pre b s \<nexists>\<rightarrow>\<^sub>i)"
  "errf \<nexists>\<rightarrow>\<^sub>f"
  "retf s v f \<nexists>\<rightarrow>\<^sub>f"
  "\<not>(branchf s p l f \<nexists>\<rightarrow>\<^sub>f)"
  unfolding terminal_i_def terminal_f_def
  by auto

lemma terminates_impl_exists_next_state:
  "terminates_to_i si si' \<Longrightarrow> \<not>terminal_i si \<Longrightarrow> \<exists>si'. si \<rightarrow>\<^sub>i si'"
  "terminates_to_f sf sf' \<Longrightarrow> \<not>terminal_f sf \<Longrightarrow> \<exists>sf'. sf \<rightarrow>\<^sub>f sf'"
  by (elim conjE, rotate_tac, induction rule: converse_rtranclp_induct; blast)+

lemma terminal_impl_no_next_state[simp]:
  "terminal_i si \<Longrightarrow> \<nexists>si'. si \<rightarrow>\<^sub>i si'"
  "terminal_f sf \<Longrightarrow> \<nexists>sf'. sf \<rightarrow>\<^sub>f sf'"
  apply (cases si, simp)
  using step_i.cases apply fast
  using step_i.cases apply fast
  apply (cases sf, simp)
  using step_f.cases apply fast
  using step_f.cases apply fast
  done

lemma terminal_steps_refl[simp]:
  "si \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> si \<rightarrow>\<^sub>i* si' \<longleftrightarrow> si'=si"
  "sf \<nexists>\<rightarrow>\<^sub>f \<Longrightarrow> sf \<rightarrow>\<^sub>f* sf' \<longleftrightarrow> sf'=sf"
  apply (auto elim: converse_rtranclpE; metis converse_rtranclpE terminal_impl_no_next_state(1))
  apply (auto elim: converse_rtranclpE; metis converse_rtranclpE terminal_impl_no_next_state(2))
  done


section "Determinism"

lemma step_deterministic[simp]:
  "si \<rightarrow>\<^sub>i si' \<Longrightarrow> \<forall>s'. si \<rightarrow>\<^sub>i s' \<longrightarrow> s' = si'"
  "sf \<rightarrow>\<^sub>f sf' \<Longrightarrow> \<forall>s'. sf \<rightarrow>\<^sub>f s' \<longrightarrow> s' = sf'"
   apply (induction arbitrary: rule: step_i_step_f.inducts)
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  subgoal premises prems for f fu b s p s' s'' v' pre n ty ins t
  proof -
    have "step_f\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)"
      by (metis (no_types, lifting) mono_rtranclp prems(4))

    then have "\<And>s''' v'' f'. branchf s' None b f \<rightarrow>\<^sub>f* retf s''' v'' f' \<longrightarrow> (s''' = s'' \<and> v'' = v' \<and> f' = f)"
      using prems(4) 
      apply (induction rule: converse_rtranclp_induct)
       apply (metis function_state.inject(2) terminal_impl_no_next_state(2) converse_rtranclpE terminal_state_simps(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct(1) step_f.cases)

    moreover

    have "\<not>(branchf s' None b f) \<rightarrow>\<^sub>f* errf"
      using prems(4) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(2) terminal_state_simps(5) converse_rtranclpE function_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct step_f.cases)

    ultimately

    show ?thesis
      using prems step_i.simps
      by auto
  qed
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  subgoal premises prems for f fu b s p s' pre n ty ins t
  proof -
    have "branchf s' None b f \<rightarrow>\<^sub>f* errf"
      by (metis (no_types, lifting) mono_rtranclp prems(4))

    moreover

    have "\<And>s'' v'. \<not>(branchf s' None b f) \<rightarrow>\<^sub>f* retf s'' v' f"
      using prems(4)
      apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(2) terminal_state_simps(4) converse_rtranclpE function_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct step_f.cases)

    ultimately

    show ?thesis
      using step_i.simps prems
      by auto
  qed
  subgoal premises prems for f fu b s p s' s'' v' pre n ty ins t
  proof -
    have "step_f\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)"
      by (metis (no_types, lifting) mono_rtranclp prems(4))

    then have "\<And>s''' v'' f'. branchf s' None b f \<rightarrow>\<^sub>f* retf s''' v'' f' \<longrightarrow> (s''' = s'' \<and> v'' = v' \<and> f' = f)"
      using prems(4) 
      apply (induction rule: converse_rtranclp_induct)
       apply (metis function_state.inject(2) terminal_impl_no_next_state(2) converse_rtranclpE terminal_state_simps(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct(1) step_f.cases)

    moreover

    have "\<not>(branchf s' None b f) \<rightarrow>\<^sub>f* errf"
      using prems(4) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(2) terminal_state_simps(5) converse_rtranclpE function_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct step_f.cases)

    ultimately

    show ?thesis
      using prems step_i.simps
      by auto
  qed
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  subgoal premises prems for f fu lab b prev s s' l
  proof -
    have "execi prev b s \<rightarrow>\<^sub>i* flowi s' (branch_label l)"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    then have "\<And>s'' br. execi prev b s \<rightarrow>\<^sub>i* flowi s'' br \<longrightarrow> (s'' = s' \<and> br = branch_label l)"
      using prems(3) 
      apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) instruction_state.inject(2) converse_rtranclpE terminal_state_simps(1))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct(1) step_i.cases)

    moreover

    have "\<not>execi prev b s \<rightarrow>\<^sub>i* erri"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) terminal_state_simps(1) converse_rtranclpE instruction_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct step_i.cases)

    ultimately

    show ?thesis
      using prems step_f.simps
      by fastforce
  qed
  subgoal premises prems for f fu lab b prev s s' v
  proof -
    have "execi prev b s \<rightarrow>\<^sub>i* flowi s' (return_value v)"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    then have "\<And>s'' br. execi prev b s \<rightarrow>\<^sub>i* flowi s'' br \<longrightarrow> (s'' = s' \<and> br = return_value v)"
      using prems(3) 
      apply (induction rule: converse_rtranclp_induct)
      apply (metis instruction_state.inject(2) terminal_impl_no_next_state(1) converse_rtranclpE Steps.terminal_state_simps(1))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct(1) step_i.cases)

    moreover

    have "\<not>execi prev b s \<rightarrow>\<^sub>i* erri"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) terminal_state_simps(1) converse_rtranclpE instruction_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct step_i.cases)

    ultimately

    show ?thesis
      using prems step_f.simps
      by fastforce
  qed
  subgoal premises prems for f fu lab b prev s
  proof -
    have "execi prev b s \<rightarrow>\<^sub>i* erri"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    moreover

    have "\<And>s' br. \<not>execi prev b s \<rightarrow>\<^sub>i* flowi s' br"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) terminal_state_simps(2) converse_rtranclpE instruction_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct step_i.cases)

    ultimately

    show ?thesis
      using prems step_f.simps
      by fastforce
  qed
  using step_f.cases apply fastforce
  using step_f.cases by fastforce



section "Weakest Precondition over Steps"

definition "wp_steps_i s Q \<equiv> \<forall>s'. terminates_to_i s s' \<longrightarrow> \<not>is_erri s' \<and> Q s'"
definition "wp_steps_f_post s s' Q \<equiv> (\<not>is_errf s') \<and> (Q (state s) (state s') (ret_value s'))"
definition "wp_steps_f s Q \<equiv> \<forall>s'. terminates_to_f s s' \<longrightarrow> wp_steps_f_post s s' Q"



section "Annotations"

type_synonym precondition = "state \<Rightarrow> bool"
type_synonym postcondition = "state \<Rightarrow> state \<Rightarrow> llvm_value option \<Rightarrow> bool"
type_synonym block_preconditions = "((llvm_identifier * llvm_identifier) * (state \<Rightarrow> state \<Rightarrow> bool)) list"
type_synonym annotations = "(llvm_identifier * (precondition * block_preconditions * postcondition)) list"

context
  fixes annotations :: "annotations"
begin


definition "global_verification_condition \<equiv>
  ((\<forall>f fu fpre bpres fpost l s.
    map_of program f = Some fu \<and>
    map_of annotations f = Some (fpre, bpres, fpost) \<and>
    first_label fu = Some l \<and> 
    fpre s
    \<longrightarrow> wp_steps_f (branchf s None l f) fpost)
  \<and> (\<forall>f. map_of program f \<noteq> None \<longrightarrow> map_of annotations f \<noteq> None))"




section "Replace Calls"

inductive
  step_i_replaced_calls :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool"
and
  step_f_replaced_calls :: "function_state \<Rightarrow> function_state \<Rightarrow> bool"
where
(* Control flow *)
"step_i_replaced_calls (execi pre ([],[],br_label l) s) (flowi s (branch_label l))"

| "dereference s b = ok (vi1 b') \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],br_i1 b l1 l2) s) (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. dereference s b = ok (vi1 b') \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],br_i1 b l1 l2) s) erri"

| "step_i_replaced_calls (execi pre ([],[],ret None) s) (flowi s (return_value None))"

| "dereference s v = ok v' \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],ret (Some (t, v))) s) (flowi s (return_value (Some v')))"
| "dereference s v = err _ \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],ret (Some (t, v))) s) erri"

(* Function calls *)
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> fpre s'
  \<Longrightarrow> fpost s' s'' v'
  \<Longrightarrow> restore_state s s''  v' na = ok s'''
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) (execi pre ([],is,t) s''')"

| "map_of program f = None
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = None
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = err _
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call n ty f p)#is,t) s) erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> fpre s'
  \<Longrightarrow> fpost s' s'' v'
  \<Longrightarrow> restore_state s s''  v' na = err _
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) erri"

| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> \<not>fpre s'
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) si'"

| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> map_of annotations f = None
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) si'"

(* Normal instructions *)
| "execute_instruction i s = ok s'
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],i#is,t) s) (execi pre ([],is,t) s')"
| "execute_instruction i s = err _
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],i#is,t) s) erri"

(* Phi nodes *)
| "execute_phi pre p s = ok s' \<Longrightarrow>
    step_i_replaced_calls (execi pre (p#ps,is,t) s) (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    step_i_replaced_calls (execi pre (p#ps,is,t) s) erri"

(* Blocks *)
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_replaced_calls\<^sup>*\<^sup>* (execi prev b s) (flowi s' (branch_label l)) \<Longrightarrow>                                                         
    step_f_replaced_calls (branchf s prev lab f) (branchf s' (Some lab) l f)"
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_replaced_calls\<^sup>*\<^sup>* (execi prev b s) (flowi s' (return_value v)) \<Longrightarrow>
    step_f_replaced_calls (branchf s prev lab f) (retf s' v f)"

(* Block errors *)
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_replaced_calls\<^sup>*\<^sup>* (execi prev b s) erri \<Longrightarrow>
    step_f_replaced_calls (branchf s prev lab f) errf"
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = None \<Longrightarrow>
     step_f_replaced_calls (branchf s prev lab f) errf"
| "map_of program f = None \<Longrightarrow>
     step_f_replaced_calls (branchf s prev lab f) errf"


fun n_rcf_steps where
  "n_rcf_steps 0 s s' = (s = s')"
| "n_rcf_steps (Suc n) s s' = (\<exists>x. step_f_replaced_calls s x \<and> n_rcf_steps n x s')"

lemma obtain_n_rcf_steps:
  assumes "step_f_replaced_calls\<^sup>*\<^sup>* s s'"
  shows "\<exists>n. n_rcf_steps n s s'"
  using assms
  apply (induction rule: converse_rtranclp_induct)
  using n_rcf_steps.simps by blast+


definition "wp_func_replaced_calls s Q \<equiv> \<forall>s'. (step_f_replaced_calls\<^sup>*\<^sup>* s s' \<and> (s' \<nexists>\<rightarrow>\<^sub>f)) \<longrightarrow> wp_steps_f_post s s' Q"

definition "call_verification_condition \<equiv>
  ((\<forall>f fu fpre bpres fpost l s.
    map_of program f = Some fu \<and> 
    map_of annotations f = Some (fpre, bpres, fpost) \<and>
    first_label fu = Some l \<and> 
    fpre s
    \<longrightarrow> wp_func_replaced_calls (branchf s None l f) fpost)
  \<and> (\<forall>f. map_of program f \<noteq> None \<longrightarrow> map_of annotations f \<noteq> None))"



lemma step_impl_step_replaced:
  assumes "call_verification_condition"
  shows "step_i si si' \<Longrightarrow> step_i_replaced_calls si si'"
    and "step_f sf sf' \<Longrightarrow> step_f_replaced_calls sf sf'"
proof (induction rule: step_i_step_f.inducts)
  case (1 pre l s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (2 s b b' pre l1 l2)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (3 s b pre l1 l2)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (4 pre s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (5 s v v' pre t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (6 s v uu pre t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (7 f fu b s p s' s'' v' pre n ty "is" t)
 \<comment> \<open> our IH: it holds for the function we call \<close>
  then have IH_f: "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)"
    using mono_rtranclp
    by (metis (no_types, lifting))

  then show ?case
    \<comment> \<open> depending on if we have annotations\<close>
    proof (cases "map_of annotations f = None")
      case True
      \<comment> \<open> if not - we can step to ANY next state (nondeterministic), so that includes the proper state we need \<close>
      \<comment> \<open> this is safe for our verification since that ALSO means it can step to an error,
           which means our verification conditions cannot proved if there are no annotations \<close>
      then show ?thesis
        using 7 step_i_replaced_calls_step_f_replaced_calls.intros
        by meson
    next
      case False
      \<comment> \<open> if we have annotations - obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        unfolding call_verification_condition_def
        by fast

      then show ?thesis
      \<comment> \<open> depending on if the precondition holds at this point \<close>
      proof (cases "fpre s'")
        case True
       \<comment> \<open> the precondition holds, which means the pre/post pair holds (per the verification condition) \<close>
       then have "wp_func_replaced_calls (branchf s' None b f) fpost"
          using assms 7 annots
          unfolding call_verification_condition_def
          by blast

       \<comment> \<open> extract the postcondition \<close>
       hence "wp_steps_f_post (branchf s' None b f) (retf s'' v' f) fpost"
          unfolding wp_func_replaced_calls_def 
          using IH_f terminal_f_def by simp
       hence post_holds: "fpost s' s'' v'"
          unfolding wp_steps_f_post_def by simp

        \<comment> \<open> and then we have our thesis - we have the postcondition just like in the replaced step relation \<close>
        then show ?thesis
          using 7 True annots step_i_replaced_calls_step_f_replaced_calls.intros
          by meson
      next
        case False
        \<comment> \<open> if not - we again do not know the next state so we can step to ANY state, safe for the same reason as before \<close>
        then show ?thesis
          using 7 annots step_i_replaced_calls_step_f_replaced_calls.intros
          by meson
      qed
    qed
next
  case (8 f pre n ty p "is" t s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (9 f fu pre n ty p "is" t s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (10 f fu b s p uv pre n ty "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (11 f fu b s p s' pre n ty "is" t)
  \<comment> \<open> our IH: it holds for the called function \<close>
  then have IH_f: "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s' None b f) errf"
    using mono_rtranclp
    by (metis (no_types, lifting))

  then show ?case
    \<comment> \<open> once again split based on whether we have annotations \<close>
    proof (cases "map_of annotations f = None")
      case True
      \<comment> \<open> if not - we can step to any next state including err \<close>
      then show ?thesis
        by (simp add: 11 step_i_replaced_calls_step_f_replaced_calls.intros)
    next
      case False
      \<comment> \<open> if we do, obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        by fast
      
      \<comment> \<open> and show this means we do not satisfy the precondition \<close>
      then have "\<not> fpre s'"
      proof -
        \<comment> \<open> if we did have the precond, then the weakest precondition over steps would hold by our vc  \<close>
        have "fpre s' \<Longrightarrow> wp_func_replaced_calls (branchf s' None b f) fpost"
          using assms 11 annots
          unfolding call_verification_condition_def
          by blast
        \<comment> \<open> which means it holds for an error \<close>
        hence "fpre s' \<Longrightarrow> wp_steps_f_post (branchf s' None b f) errf fpost"
          unfolding wp_func_replaced_calls_def 
          using IH_f terminal_f_def
          by simp
        \<comment> \<open> however, that is a contradiction since wp specifies it does not reach errors \<close>
        then show ?thesis
          unfolding wp_steps_f_post_def by fastforce
      qed

      \<comment> \<open> since we don't have the precondition, we can transition to any state including err \<close>
      then show ?thesis
        using 11 annots step_i_replaced_calls_step_f_replaced_calls.intros
        by meson
    qed
next
  case (12 f fu b s p s' s'' v' pre n ty "is" t)
 \<comment> \<open> our IH: it holds for the function we call \<close>
  then have IH_f: "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)"
    using mono_rtranclp
    by (metis (no_types, lifting))

  then show ?case
    \<comment> \<open> depending on if we have annotations\<close>
    proof (cases "map_of annotations f = None")
      case True
      \<comment> \<open> if not - we can step to ANY next state (nondeterministic), so that includes the proper state we need \<close>
      \<comment> \<open> this is safe for our verification since that ALSO means it can step to an error,
           which means our verification conditions cannot proved if there are no annotations \<close>
      then show ?thesis
        using 12 step_i_replaced_calls_step_f_replaced_calls.intros
        by meson
    next
      case False
      \<comment> \<open> if we have annotations - obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        unfolding call_verification_condition_def
        by fast

      then show ?thesis
      \<comment> \<open> depending on if the precondition holds at this point \<close>
      proof (cases "fpre s'")
        case True
       \<comment> \<open> the precondition holds, which means the pre/post pair holds (per the verification condition) \<close>
       then have "wp_func_replaced_calls (branchf s' None b f) fpost"
          using assms 12 annots
          unfolding call_verification_condition_def
          by blast

       \<comment> \<open> extract the postcondition \<close>
       hence "wp_steps_f_post (branchf s' None b f) (retf s'' v' f) fpost"
          unfolding wp_func_replaced_calls_def 
          using IH_f terminal_f_def by simp
       hence post_holds: "fpost s' s'' v'"
          unfolding wp_steps_f_post_def by simp

        \<comment> \<open> and then we have our thesis - we have the postcondition just like in the replaced step relation \<close>
        then show ?thesis
          using 12 True annots step_i_replaced_calls_step_f_replaced_calls.intros
          by meson
      next
        case False
        \<comment> \<open> if not - we again do not know the next state so we can step to ANY state, safe for the same reason as before \<close>
        then show ?thesis
          using 12 annots step_i_replaced_calls_step_f_replaced_calls.intros
          by meson
      qed
    qed
next
  case (13 i s s' pre "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (14 i s uw pre "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (15 pre p s s' ps "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (16 pre p s ux ps "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (17 f fu lab b prev s s' l)
  then show ?case
    using mono_rtranclp step_i_replaced_calls_step_f_replaced_calls.intros
    by (metis (no_types, lifting))
next
  case (18 f fu lab b prev s s' v)
  then show ?case
    using mono_rtranclp step_i_replaced_calls_step_f_replaced_calls.intros
    by (metis (no_types, lifting))
next
  case (19 f fu lab b prev s)
  then show ?case
    using mono_rtranclp step_i_replaced_calls_step_f_replaced_calls.intros
    by (metis (no_types, lifting))
next
  case (20 f fu lab s prev)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (21 f s prev lab)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
qed


lemma unfolded_wp_vc:
  assumes "call_verification_condition"
  assumes "map_of program f = Some fu"
  assumes "map_of annotations f = Some (fpre, bpres, fpost)"
  assumes "first_label fu = Some l"
  assumes "fpre s"
  assumes "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s None l f) s'"
  assumes "s' \<nexists>\<rightarrow>\<^sub>f"
  shows "wp_steps_f_post (branchf s None l f) s' fpost"
  by (smt (verit, best) wp_func_replaced_calls_def assms call_verification_condition_def)


lemma call_vc_impl_global_vc:
  "call_verification_condition \<Longrightarrow> global_verification_condition"
  unfolding global_verification_condition_def wp_steps_f_def
  apply (intro allI conjI impI)
   apply (smt (verit, ccfv_threshold) mono_rtranclp step_impl_step_replaced(2) unfolded_wp_vc)
  unfolding call_verification_condition_def
  by blast


section "Floyd Method"

definition "has_annotation fs \<equiv>
  (case fs of
    errf \<Rightarrow> False
  | retf _ _ f \<Rightarrow> map_of program f \<noteq> None \<and> map_of annotations f \<noteq> None
  | branchf _ p l f \<Rightarrow> (case map_of program f of
      None \<Rightarrow> False
    | Some fu \<Rightarrow>
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre, bpres, fpost) \<Rightarrow>
        (case p of
          None \<Rightarrow> (case first_label fu of
            Some lab \<Rightarrow> l = lab
          | None \<Rightarrow> False)
        | Some prev \<Rightarrow> map_of bpres (prev, l) \<noteq> None
        )
      )
    )
  )"

definition "annotation_holds init fs \<equiv>
  (case fs of
    errf \<Rightarrow> False
  | retf s v f \<Rightarrow> 
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre, bpres, fpost) \<Rightarrow> map_of program f \<noteq> None \<and> fpre init \<and> fpost init s v
      )
  | branchf s p l f \<Rightarrow> (case map_of program f of
      None \<Rightarrow> False
    | Some fu \<Rightarrow>
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre, bpres, fpost) \<Rightarrow>
          (case p of
            None \<Rightarrow> (case first_label fu of
              None \<Rightarrow> False
            | Some lab \<Rightarrow> l = lab \<and> fpre s \<and> s = init)
          | Some prev \<Rightarrow> 
              (case map_of bpres (prev, l) of
                None \<Rightarrow> False
              | Some pre \<Rightarrow> fpre init \<and> pre init s
              )
          )
      )
    )
  )"

definition step_until :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" where
  "step_until fs fs' \<equiv> step_f_replaced_calls fs fs' \<and> \<not>has_annotation fs"

definition annotated_step :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "s \<Rightarrow> s' \<equiv> (\<exists>x. step_f_replaced_calls s x \<and> step_until\<^sup>*\<^sup>* x s') \<and> (has_annotation s' \<or> is_errf s')"

abbreviation annotated_steps :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>*" 50) where
  "fs \<Rightarrow>* fs' \<equiv> annotated_step\<^sup>*\<^sup>* fs fs'"

definition wp_step where
  "wp_step fs Q \<equiv> (\<forall>fs'. step_f_replaced_calls fs fs' \<longrightarrow> \<not>is_errf fs' \<and> Q fs')"

definition wp_rc_steps_i where
  "wp_rc_steps_i s Q \<equiv> (\<forall>s'. (step_i_replaced_calls\<^sup>*\<^sup>* s s' \<and> s' \<nexists>\<rightarrow>\<^sub>i) \<longrightarrow> (\<not>is_erri s' \<and> Q s'))"
definition wp_rc_step_i where
  "wp_rc_step_i s Q \<equiv> (\<forall>s'. (step_i_replaced_calls s s') \<longrightarrow> (\<not>is_erri s' \<and> Q s'))"

lemma wp_rc_steps_i_intro:
  assumes "s \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> \<not>is_erri s \<and> Q s"
  assumes "\<not>s \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> wp_rc_step_i s (\<lambda>s'. wp_rc_steps_i s' Q)"
  shows "wp_rc_steps_i s Q"
  unfolding wp_rc_steps_i_def
  apply (intro allI impI, elim conjE)
  subgoal for s'
    using assms apply (rotate_tac 0)
    apply (induction rule: converse_rtranclp_induct) apply blast
    unfolding wp_rc_step_i_def
    by (smt (verit) Steps.step_i_replaced_calls.simps terminal_state_simps(3) wp_rc_steps_i_def)
  done

lemma wp_step_intro:
  assumes "map_of program f = Some fu"
  assumes "map_of (llvm_function.blocks fu) lab = Some b"
  assumes "wp_rc_steps_i
            (execi prev b s)
            (\<lambda>si'.
              (case si' of
                flowi s' br \<Rightarrow>
                  (case br of
                    branch_label l \<Rightarrow> Q (branchf s' (Some lab) l f)
                  | return_value v \<Rightarrow> Q (retf s' v f)
                  )
              | _ \<Rightarrow> False
              )
            )"
  shows "wp_step (branchf s prev lab f) Q"
  unfolding wp_step_def
  apply (intro allI impI)
  apply (cases rule: step_f_replaced_calls.cases)
  using assms
  unfolding wp_rc_steps_i_def
  by auto



named_theorems wp_step_i_intros
lemma wp_step_i_br_label_intro[wp_step_i_intros]:
  assumes "Q (flowi s (branch_label l))"
  shows "wp_rc_step_i (execi pre ([],[],br_label l) s) Q"
  using assms
  unfolding wp_rc_step_i_def
  apply (intro allI impI)
  using step_i_replaced_calls.simps
  by simp
lemma wp_step_i_br_i1_intro[wp_step_i_intros]:
  assumes "register_\<alpha> s b = Some (vi1 bool)"
  assumes "bool \<Longrightarrow> Q (flowi s (branch_label l1))"
  assumes "\<not>bool \<Longrightarrow> Q (flowi s (branch_label l2))"
  shows "wp_rc_step_i (execi pre ([],[],br_i1 b l1 l2) s) Q"
  using assms
  unfolding wp_rc_step_i_def
  apply (intro allI impI)
  using step_i_replaced_calls.simps register_\<alpha>_eq_get_register
  by (cases bool; fastforce) \<comment> \<open> Takes a bit... \<close>
lemma wp_step_i_ret_None_intro[wp_step_i_intros]:
  assumes "Q (flowi s (return_value None))"
  shows "wp_rc_step_i (execi pre ([],[],ret None) s) Q"
  using assms
  unfolding wp_rc_step_i_def
  apply (intro allI impI)
  using step_i_replaced_calls.simps
  by simp
lemma wp_step_i_ret_value_intro[wp_step_i_intros]:
  assumes "register_\<alpha> s v = Some v'"
  assumes "Q (flowi s (return_value (Some v')))"
  shows "wp_rc_step_i (execi pre ([],[],ret (Some (t,v))) s) Q"
  using assms
  unfolding wp_rc_step_i_def
  apply (intro allI impI)
  using step_i_replaced_calls.simps register_\<alpha>_eq_get_register
  by simp
lemma wp_step_i_phi_intro[wp_step_i_intros]:
  assumes "wp (execute_phi pre p s) (\<lambda>s'. Q (execi pre (ps,is,ter) s'))"
  shows "wp_rc_step_i (execi pre (p#ps,is,ter) s) Q"
proof -
  obtain s' where "execute_phi pre p s = ok s'"
    using assms unfolding wp_def by (auto split: result.splits)
  then have "Q (execi pre (ps,is,ter) s')" using assms unfolding wp_def by simp
  then show ?thesis
    unfolding wp_rc_step_i_def using step_i_replaced_calls.simps \<open>execute_phi pre p s = ok s'\<close>
    by force
qed
lemma wp_step_i_instr_intro[wp_step_i_intros]:
  assumes "is_call i \<Longrightarrow> i = call na ty f p"
  assumes "is_call i \<Longrightarrow> map_of program f = Some fu"
  assumes "is_call i \<Longrightarrow> first_label fu = Some b"
  assumes "is_call i \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)"
  assumes "is_call i \<Longrightarrow> wp (prepare_state s (params fu) p) (\<lambda>s'. fpre s' \<and> (\<forall>s'' v'. fpost s' s'' v' \<longrightarrow> wp (restore_state s s'' v' na) (\<lambda>s'''. Q (execi pre ([],is,ter) s''') )))"
  assumes "\<not>is_call i \<Longrightarrow> wp (execute_instruction i s) (\<lambda>s'. Q (execi pre ([],is,ter) s'))"
  shows "wp_rc_step_i (execi pre ([],i#is,ter) s) Q"
  unfolding wp_rc_step_i_def apply (intro allI impI) subgoal premises prems for si'
proof (cases "is_call i")
  case True

  have step: "step_i_replaced_calls (execi pre ([],(call na ty f p)#is,ter) s) si'"
    using True assms prems
    by blast

  obtain sprep where
    prepok: "prepare_state s (params fu) p = ok sprep" and
    preholds: "fpre sprep" 
    using assms prems True
    unfolding wp_def
    by (auto split: result.splits)

  obtain s'' v' s''' where
    postholds: "fpost sprep s'' v'" and
    restok: "restore_state s s'' v' na = ok s'''" and
    si_eq: "si' = (execi pre ([],is,ter) s''')"
    using step True assms prepok preholds
    apply (cases rule: step_i_replaced_calls.cases; (simp del: split_paired_All))
    unfolding wp_def
    apply (simp del: split_paired_All split: result.splits)
    by blast

  have "Q (execi pre ([],is,ter) s''')" 
    using step True assms prepok preholds postholds restok
    unfolding wp_def
    apply (simp del: split_paired_All)
    apply (erule allE[where x=s''])
    by auto

  then show ?thesis using si_eq
    by simp
next
  case False
  then obtain s' where "execute_instruction i s = ok s'"
    using assms unfolding wp_def by (auto split: result.splits)
  then have "Q (execi pre ([],is,ter) s')" using assms False unfolding wp_def by simp
  then show ?thesis
    unfolding wp_rc_step_i_def using step_i_replaced_calls.simps \<open>execute_instruction i s = ok s'\<close> False prems
    by force \<comment> \<open> Takes a bit... \<close>
qed
  done


definition wp_steps_until where
  "wp_steps_until fs Q \<equiv> (\<forall>fs'. step_until\<^sup>*\<^sup>* fs fs' \<and> \<not>is_errf fs \<longrightarrow> \<not>is_errf fs') \<and> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> has_annotation fs' \<longrightarrow> Q fs')"

definition wp_annotated_step where
  "wp_annotated_step fs Q \<equiv> (\<forall>fs'. ((fs \<Rightarrow> fs') \<longrightarrow> (\<not>is_errf fs' \<and> Q fs')))"

definition "floyd_cond init s p l f \<equiv> wp_annotated_step (branchf s p l f) (\<lambda>fs'. annotation_holds init fs')"

definition floyd_vc :: "bool" where
  "floyd_vc \<equiv> \<forall>f. (map_of program f \<noteq> None) \<longrightarrow> 
    (case map_of annotations f of
      None \<Rightarrow> False 
    | Some (fpre, bpres, fpost) \<Rightarrow> (
        (first_label (the (map_of program f)) \<noteq> None) \<and>
        (\<forall>init. fpre init \<longrightarrow> (
            floyd_cond init init None (the (first_label (the (map_of program f)))) f
          \<and> (\<forall>pred l. map_of bpres (pred, l) \<noteq> None \<longrightarrow> 
              (\<forall>s. annotation_holds init (branchf s (Some pred) l f) \<longrightarrow> 
                floyd_cond init s (Some pred) l f)
            )
          )
        )
      )
    )"




lemma step_until_closure_to_annotated_step:
  assumes "step_f_replaced_calls fs x"
  assumes "step_until\<^sup>*\<^sup>* x fs'"
  assumes "has_annotation fs' \<or> is_errf fs'"
  shows "fs \<Rightarrow> fs'"
  unfolding annotated_step_def
  using assms
  by blast


lemma wp_annotated_step_intro:
  assumes "wp_step fs (\<lambda>fs'. wp_steps_until fs' Q)"
  shows "wp_annotated_step fs Q"
  using assms
  unfolding wp_annotated_step_def wp_step_def wp_steps_until_def annotated_step_def
  by blast

lemma wp_steps_until_intro:
  assumes "has_annotation fs \<Longrightarrow> Q fs"
  assumes "\<not>has_annotation fs \<Longrightarrow> wp_step fs (\<lambda>fs'. wp_steps_until fs' Q)"
  shows "wp_steps_until fs Q"
  using assms
  unfolding wp_steps_until_def wp_step_def
  apply (cases "has_annotation fs")
  using step_until_def converse_rtranclpE
  by metis+

lemma annotation_holds_impl_annotation_holds_single_step:
  assumes "floyd_vc"
  assumes "annotation_holds init sf"
  assumes "sf \<Rightarrow> sf'"
  shows "annotation_holds init sf'"
  apply (cases sf) 
  subgoal for s p l f
    using assms(2)
    apply (cases "map_of program f"; cases "map_of annotations f")
    subgoal apply (unfold annotation_holds_def) by simp
    subgoal apply (unfold annotation_holds_def) by simp
    subgoal apply (unfold annotation_holds_def) by simp
    subgoal for fu annots apply simp
      apply (cases annots; simp)
      subgoal premises prems for fpre bpres fpost
      proof (cases p)
        case None

        have firstlab: "first_label fu = Some l"
          using None prems
          unfolding annotation_holds_def
          by (simp split: option.splits)

        have preholds: "fpre s" 
          using assms(2) prems(1,3,4) None firstlab
          unfolding annotation_holds_def
          by auto

        show ?thesis
          using assms(1)
          unfolding floyd_vc_def
          apply -
          apply (erule allE[where x=f])
          apply (erule impE) using prems apply blast
          apply (cases "map_of annotations f") apply simp
          apply (simp del: split_paired_All)
          apply (erule conjE)
          subgoal for annots
            apply (cases annots)
            apply (simp del: split_paired_All)
            subgoal for fpre' bpres' fpost'
              apply (erule allE[where x=init]) apply (erule impE)
                subgoal
                  using assms(2) None prems
                  unfolding annotation_holds_def
                  by auto
              apply (erule conjE)
              unfolding floyd_cond_def
              using None firstlab assms prems
              unfolding wp_annotated_step_def annotation_holds_def
              by auto
            done
          done
      next
        case (Some pred)
        then show ?thesis
          using assms(1)
          unfolding floyd_vc_def
          apply -
          apply (erule allE[where x=f])
          apply (erule impE) using prems apply blast
          apply (cases "map_of annotations f") apply simp
          apply (simp del: split_paired_All)
          apply (erule conjE)
          subgoal for annots
            apply (cases annots)
            apply (simp del: split_paired_All)
            subgoal for fpre' bpres' fpost'
              apply (erule allE[where x=init]) apply (erule impE)
                subgoal
                  using assms(2) Some prems
                  unfolding annotation_holds_def
                  by (auto split: option.splits)
              apply (erule conjE)
              apply (thin_tac "floyd_cond init init _ _ _")
              apply (erule allE[where x=pred])
              apply (erule allE[where x=l])
              apply (erule impE)
              subgoal
                using prems
                unfolding annotation_holds_def
                by (simp split: option.splits)
              apply (erule allE[where x=s])
              unfolding floyd_cond_def
              using assms(2,3) prems(1) wp_annotated_step_def
              by blast
            done
          done
        qed
      done
    done
  subgoal for s v f 
    using assms
    unfolding annotated_step_def
    by (simp add: Steps.step_f_replaced_calls.simps)
  using assms
  unfolding annotation_holds_def
  by simp



lemma annotation_holds_impl_annotation_holds_multi_step:
  assumes "sf \<Rightarrow>* sf'"
  assumes "floyd_vc"
  assumes "annotation_holds init sf"
  shows "annotation_holds init sf'"
  using assms
  apply (induction rule: rtranclp_induct)
   apply blast
  using annotation_holds_impl_annotation_holds_single_step
  by blast



lemma exists_first_cutpoint:
  assumes "n_rcf_steps n s s'"
  assumes "has_annotation s' \<or> is_errf s'"
  shows "\<exists>x m. step_until\<^sup>*\<^sup>* s x \<and> (has_annotation x \<or> is_errf x) \<and> n_rcf_steps m x s' \<and> m \<le> n"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain x where xdef: "n_rcf_steps n x s' \<and> step_f_replaced_calls s x" by auto
  then show ?case
    by (metis converse_rtranclp_into_rtranclp le_refl less_Suc_eq_le nat_less_le
        rtranclp.rtrancl_refl step_until_def Suc)
qed


lemma steps_impl_annotated_steps:
  assumes "step_f_replaced_calls\<^sup>*\<^sup>* sf sf'"
  assumes "has_annotation sf' \<or> is_errf sf'"
  shows "sf \<Rightarrow>* sf'"
  using assms
proof -
  obtain n where ndef: "n_rcf_steps n sf sf'"
    using assms obtain_n_rcf_steps
    by blast
  then show ?thesis
  proof (induction n arbitrary: sf rule: less_induct)
    case (less n sf)
    then show ?case proof (cases n)
      case 0
      then show ?thesis
        using less
        by simp
    next
      case (Suc nat)
      
      obtain s1 where "step_f_replaced_calls sf s1" and "n_rcf_steps nat s1 sf'"
        using less ndef Suc
        by auto

      then obtain s2 m where steps: "step_until\<^sup>*\<^sup>* s1 s2 \<and> (has_annotation s2 \<or> is_errf s2) \<and> n_rcf_steps m s2 sf' \<and> m \<le> nat"
        using exists_first_cutpoint less assms
        by blast          
      then have "sf \<Rightarrow> s2"
        using \<open>step_f_replaced_calls sf s1\<close> step_until_closure_to_annotated_step
        by blast
      then show ?thesis
        by (metis Suc steps converse_rtranclp_into_rtranclp less.IH less_Suc_eq_le)
    qed
  qed
qed

lemma annotated_step_keeps_function_ret:
  assumes "step_f_replaced_calls\<^sup>*\<^sup>* sf (retf s' v f')"
  assumes "sf = (branchf s p l f)"
  shows "f' = f"
  using assms
  apply (induction arbitrary: s p l f rule: converse_rtranclp_induct) apply blast
  by (smt (verit) converse_rtranclpE function_state.distinct(1,6) function_state.inject(1)
      function_state.sel(7) step_f_replaced_calls.simps
      terminal_state_simps(4,6))
  

lemma floyd_vc_impl_call_vc:
  assumes "floyd_vc"
  shows "call_verification_condition"
  unfolding call_verification_condition_def
  apply (rule conjI) defer apply (rule allI)
  subgoal for f
    using assms
    unfolding floyd_vc_def
    apply -
    apply (erule allE[where x=f])
    by (auto split: option.splits)
  apply (intro allI)
  subgoal for f fu fpre bpres fpost l s
    apply (intro impI)
    apply (elim conjE)
    unfolding wp_func_replaced_calls_def
    apply (intro allI impI) apply (erule conjE)
    subgoal premises prems for s'
    proof -
      have rc_path: "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s None l f) s'"
        using prems
        by blast

      have s'_ter: "s' \<nexists>\<rightarrow>\<^sub>f"
        using prems
        by blast

      have init_annot: "annotation_holds s (branchf s None l f)"
        using assms
        unfolding floyd_vc_def
        apply -
        apply (erule allE[where x=f])
        apply auto
        using prems apply simp
        apply (simp split: option.splits del: split_paired_All)
        subgoal for annots
          apply (cases annots) apply (simp del: split_paired_All)
          apply (elim conjE) apply (erule allE[where x=s])
          subgoal for fpre' bpres' fpost'
            apply (elim impE)
            using prems apply simp
            unfolding annotation_holds_def
            apply (auto split: option.splits)
            using prems
            by auto
          done
        done
      
      have annotated: "has_annotation s' \<or> is_errf s'"
      proof (cases s')
        case (branchf x11 x12 x13 x14)
        then show ?thesis
          using s'_ter
          by force
      next
        case (retf state val func)
        obtain start where path: "step_f_replaced_calls\<^sup>*\<^sup>* start s'" and startdef: "start \<noteq> retf state val func"
          using rc_path
          by blast

        have "func = f" using path retf
          apply (induction rule: rtranclp_induct) using startdef apply blast
          using annotated_step_keeps_function_ret rc_path retf by blast
        
        then show ?thesis
          using prems has_annotation_def retf by fastforce
      next
        case errf
        then show ?thesis 
          by simp
      qed

      have "(branchf s None l f) \<Rightarrow>* s'"
        using annotated init_annot rc_path steps_impl_annotated_steps
        by blast

      then have "annotation_holds s s'"
        using annotation_holds_impl_annotation_holds_multi_step assms init_annot
        by blast

      then show ?thesis apply (cases s')
        using s'_ter terminal_state_simps(6) apply blast defer unfolding annotation_holds_def apply simp apply (auto split: option.splits)
        unfolding wp_steps_f_post_def
        by (metis (no_types, opaque_lifting) Steps.annotated_step_keeps_function_ret function_state.disc(8) function_state.sel(1,2,6) old.prod.inject option.inject
            prems(2,4,5) push_frame.cases)
    qed
    done
  done

end
end

lemma floyd_vc_impl_global_vc:
  "floyd_vc p a \<Longrightarrow> global_verification_condition p a"
  using floyd_vc_impl_call_vc call_vc_impl_global_vc
  by blast

lemma
  assumes "floyd_vc p a"
  assumes "map_of p f = Some fu"
  shows "map_of a f \<noteq> None"
  using assms
  unfolding floyd_vc_def
  apply (auto split: option.splits)
  by fastforce

lemma
  assumes "floyd_vc p a"
  assumes "map_of p f = Some fu"
  assumes "map_of a f = Some (fpre,bpres,fpost)"
  assumes "first_label fu = Some l"
  assumes "fpre s"
  assumes "terminates_to_f p (branchf s None l f) sf'"
  shows "fpost s (state sf') (ret_value sf')"
  using assms floyd_vc_impl_global_vc
  unfolding global_verification_condition_def wp_steps_f_def wp_steps_f_post_def
  by (metis function_state.sel(1) )


fun verify_blocks :: "llvm_program \<Rightarrow> annotations \<Rightarrow> block_preconditions \<Rightarrow> llvm_identifier \<Rightarrow> state \<Rightarrow> bool" where
  "verify_blocks _ _ [] _ _ = True"
| "verify_blocks p a (((prev, lab), precond) # bpres) f init = 
    ((\<forall>s. annotation_holds p a init (branchf s (Some prev) lab f) \<longrightarrow> floyd_cond p a init s (Some prev) lab f) 
     \<and> verify_blocks p a bpres f init)"

fun verify_function :: "llvm_program \<Rightarrow> annotations \<Rightarrow> llvm_identifier \<Rightarrow> llvm_function \<Rightarrow> bool" where
  "verify_function p a fl fb =
     (case map_of a fl of
        None \<Rightarrow> False 
      | Some (fpre, bpres, fpost) \<Rightarrow> 
          (first_label fb \<noteq> None \<and> 
           (\<forall>init. fpre init \<longrightarrow> 
              floyd_cond p a init init None (the (first_label fb)) fl \<and> 
              verify_blocks p a bpres fl init)))"

fun verify_program' :: "llvm_program \<Rightarrow> llvm_program \<Rightarrow> annotations \<Rightarrow> bool" where
  "verify_program' [] _ _ = True"
| "verify_program' ((fl, fb) # fs) p a = (verify_function p a fl fb \<and> verify_program' fs p a)"

fun verify_program :: "llvm_program \<Rightarrow> annotations \<Rightarrow> bool" where
  "verify_program p a = verify_program' p p a"


lemma verify_program_members:
  assumes "verify_program' fs p a"
  assumes "(fl, fb) \<in> set fs"
  shows "verify_function p a fl fb"
  using assms
  by (induction fs) auto


lemma verify_blocks_imp_floyd_cond:
  assumes "verify_blocks p a bpres f init"
  assumes "map_of bpres (pred, l) = Some precond"
  assumes "annotation_holds p a init (branchf s (Some pred) l f)"
  shows "floyd_cond p a init s (Some pred) l f"
  using assms
proof (induction bpres)
  case Nil
  then show ?case by simp
next
  case (Cons pair bpres)
  obtain prev lab pc where pair_def: "pair = ((prev, lab), pc)" apply (cases pair) by fast
  then show ?case
    using Cons
    apply (auto split: if_splits) 
    using Cons verify_blocks.simps by fast
qed


lemma verify_program_impl_floyd_vc:
  assumes "verify_program' program program annotations"
  shows "floyd_vc program annotations"
  unfolding floyd_vc_def
  apply (intro allI impI)
  subgoal for f
    apply (cases "map_of program f")
     apply simp
    subgoal premises prems for fu
    proof -
      have f_in_set: "(f, fu) \<in> set program"
        using map_of_SomeD prems
        by fast

      have "verify_function program annotations f fu"
        using assms f_in_set verify_program_members by blast

      then show ?thesis 
        using prems f_in_set
        apply (simp split: option.splits del: split_paired_All)
        apply (intro conjI) apply blast apply (elim conjE) using verify_blocks_imp_floyd_cond by blast
    qed
    done
  done

lemma verify_program_impl_global_vc:
  assumes "verify_program program annotations"
  shows "global_verification_condition program annotations"
  using assms verify_program_impl_floyd_vc floyd_vc_impl_global_vc
  by simp

end