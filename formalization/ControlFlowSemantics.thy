theory ControlFlowSemantics
  imports InstructionSemantics
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
  | error_state: errf

definition "first_label f \<equiv> (case llvm_function.blocks f of ((l,b)#fs) \<Rightarrow> Some l | _ \<Rightarrow> None)"

fun assign_params :: "(llvm_identifier * llvm_type) list \<Rightarrow> (llvm_type * llvm_value_ref) list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> state result" where
  "assign_params [] [] s s' = ok s'"
| "assign_params [] _ s s' = err invalid_parameter_length"
| "assign_params _ [] s s' = err invalid_parameter_length"
| "assign_params ((n,t)#ps) ((t',v)#vs) s s' = do {
    val \<leftarrow> get_register s v;
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

inductive
  step_i :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>i" 50)
and
  step_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f" 50)
where
(* Control flow *)
"(execi pre ([],[],br_label l) s) \<rightarrow>\<^sub>i (flowi s (branch_label l))"

| "get_register s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. get_register s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i erri"

| "(execi pre ([],[],ret None) s) \<rightarrow>\<^sub>i (flowi s (return_value None))"

| "get_register s v = ok v' \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i (flowi s (return_value (Some v')))"
| "get_register s v = err _ \<Longrightarrow>
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
      apply (metis instruction_state.inject(2) terminal_impl_no_next_state(1) converse_rtranclpE terminal_state_simps(1))
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

end

end
