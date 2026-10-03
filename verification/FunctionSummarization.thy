theory FunctionSummarization
  imports WeakestPreconditions
begin

context
  fixes program :: "llvm_program"
  fixes annotations :: "annotations"
begin

section "Replace Calls"

inductive
  step_i_summarized :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool"
and
  step_f_summarized :: "function_state \<Rightarrow> function_state \<Rightarrow> bool"
where
(* Control flow *)
"step_i_summarized (execi pre ([],[],br_label l) s) (flowi s (branch_label l))"

| "get_register s b = ok (vi1 b') \<Longrightarrow>
    step_i_summarized (execi pre ([],[],br_i1 b l1 l2) s) (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. get_register s b = ok (vi1 b') \<Longrightarrow>
    step_i_summarized (execi pre ([],[],br_i1 b l1 l2) s) erri"

| "step_i_summarized (execi pre ([],[],ret None) s) (flowi s (return_value None))"

| "get_register s v = ok v' \<Longrightarrow>
    step_i_summarized (execi pre ([],[],ret (Some (t, v))) s) (flowi s (return_value (Some v')))"
| "get_register s v = err _ \<Longrightarrow>
    step_i_summarized (execi pre ([],[],ret (Some (t, v))) s) erri"

(* Function calls *)
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> fpre s'
  \<Longrightarrow> fpost s' s'' v'
  \<Longrightarrow> restore_state s s''  v' na = ok s'''
  \<Longrightarrow> step_i_summarized (execi pre ([],(call na ty f p)#is,t) s) (execi pre ([],is,t) s''')"

| "map_of program f = None
  \<Longrightarrow> step_i_summarized (execi pre ([],(call na ty f p)#is,t) s) erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = None
  \<Longrightarrow> step_i_summarized (execi pre ([],(call na ty f p)#is,t) s) erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = err _
  \<Longrightarrow> step_i_summarized (execi pre ([],(call n ty f p)#is,t) s) erri"
| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> fpre s'
  \<Longrightarrow> fpost s' s'' v'
  \<Longrightarrow> restore_state s s''  v' na = err _
  \<Longrightarrow> step_i_summarized (execi pre ([],(call na ty f p)#is,t) s) erri"

| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> prepare_state s (params fu) p = ok s'
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> \<not>fpre s'
  \<Longrightarrow> step_i_summarized (execi pre ([],(call na ty f p)#is,t) s) si'"

| "map_of program f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> map_of annotations f = None
  \<Longrightarrow> step_i_summarized (execi pre ([],(call na ty f p)#is,t) s) si'"

(* Normal instructions *)
| "execute_instruction i s = ok s'
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_summarized (execi pre ([],i#is,t) s) (execi pre ([],is,t) s')"
| "execute_instruction i s = err _
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_summarized (execi pre ([],i#is,t) s) erri"

(* Phi nodes *)
| "execute_phi pre p s = ok s' \<Longrightarrow>
    step_i_summarized (execi pre (p#ps,is,t) s) (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    step_i_summarized (execi pre (p#ps,is,t) s) erri"

(* Blocks *)
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_summarized\<^sup>*\<^sup>* (execi prev b s) (flowi s' (branch_label l)) \<Longrightarrow>                                                         
    step_f_summarized (branchf s prev lab f) (branchf s' (Some lab) l f)"
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_summarized\<^sup>*\<^sup>* (execi prev b s) (flowi s' (return_value v)) \<Longrightarrow>
    step_f_summarized (branchf s prev lab f) (retf s' v f)"

(* Block errors *)
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_summarized\<^sup>*\<^sup>* (execi prev b s) erri \<Longrightarrow>
    step_f_summarized (branchf s prev lab f) errf"
| "map_of program f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = None \<Longrightarrow>
     step_f_summarized (branchf s prev lab f) errf"
| "map_of program f = None \<Longrightarrow>
     step_f_summarized (branchf s prev lab f) errf"



definition wp_fs_with_summarization where
  "wp_fs_with_summarization s Q \<equiv> \<forall>s'. step_f_summarized\<^sup>*\<^sup>* s s' \<and> terminal_f s' \<longrightarrow> (\<not>error_state s' \<and> Q s')"


definition wp_f_with_summarization where
  "wp_f_with_summarization fs Q \<equiv> (\<forall>fs'. step_f_summarized fs fs' \<longrightarrow> \<not>error_state fs' \<and> Q fs')"

definition wp_is_with_summarization where
  "wp_is_with_summarization s Q \<equiv> (\<forall>s'. (step_i_summarized\<^sup>*\<^sup>* s s' \<and> terminal_i s') \<longrightarrow> (\<not>is_erri s' \<and> Q s'))"

definition wp_i_with_summarization where
  "wp_i_with_summarization s Q \<equiv> (\<forall>s'. step_i_summarized s s' \<longrightarrow> (\<not>is_erri s' \<and> Q s'))"

definition "function_hoare_with_summarization pre b f post \<equiv> \<forall>s. pre s \<longrightarrow> wp_fs_with_summarization (branchf s None b f) (\<lambda>s'. post s (state s') (ret_value s'))"

definition "function_correct_with_summarization f \<equiv>
  \<forall>body pre bpres post block.
    map_of program f = Some body
  \<and> map_of annotations f = Some (pre, bpres, post)
  \<and> first_label body = Some block
  \<longrightarrow> function_hoare_with_summarization pre block f post"

definition "program_correct_with_summarization \<equiv>
  \<forall>f. map_of program f \<noteq> None
  \<longrightarrow> function_correct_with_summarization f \<and> map_of annotations f \<noteq> None"



fun n_rcf_steps where
  "n_rcf_steps 0 s s' = (s = s')"
| "n_rcf_steps (Suc n) s s' = (\<exists>x. step_f_summarized s x \<and> n_rcf_steps n x s')"

lemma obtain_n_rcf_steps:
  assumes "step_f_summarized\<^sup>*\<^sup>* s s'"
  shows "\<exists>n. n_rcf_steps n s s'"
  using assms
  apply (induction rule: converse_rtranclp_induct)
  using n_rcf_steps.simps by blast+

lemma overapproximation:
  assumes "program_correct_with_summarization"
  shows "step_i program si si' \<Longrightarrow> step_i_summarized si si'"
    and "step_f program sf sf' \<Longrightarrow> step_f_summarized sf sf'"
proof (induction rule: step_i_step_f.inducts)
  case (1 pre l s)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (2 s b b' pre l1 l2)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (3 s b pre l1 l2)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (4 pre s)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (5 s v v' pre t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (6 s v uu pre t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (7 f fu b s p s' s'' v' pre n ty "is" t)
 \<comment> \<open> our IH: it holds for the function we call \<close>
  then have IH_f: "step_f_summarized\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)"
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
        using 7 step_i_summarized_step_f_summarized.intros
        by meson
    next
      case False
      \<comment> \<open> if we have annotations - obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        unfolding program_correct_with_summarization_def
        by fast

      then show ?thesis
      \<comment> \<open> depending on if the precondition holds at this point \<close>
      proof (cases "fpre s'")
        case True
       \<comment> \<open> the precondition holds, which means the pre/post pair holds (per the verification condition) \<close>
       then have "wp_fs_with_summarization (branchf s' None b f) (\<lambda>s. fpost s' (state s) (ret_value s))"
          using assms 7 annots
          unfolding program_correct_with_summarization_def function_correct_with_summarization_def function_hoare_with_summarization_def
          by blast

       \<comment> \<open> extract the postcondition \<close>
        hence post_holds: "fpost s' s'' v'"
          using IH_f
          unfolding wp_fs_with_summarization_def
          by force

        \<comment> \<open> and then we have our thesis - we have the postcondition just like in the replaced step relation \<close>
        then show ?thesis
          using 7 True annots step_i_summarized_step_f_summarized.intros
          by meson
      next
        case False
        \<comment> \<open> if not - we again do not know the next state so we can step to ANY state, safe for the same reason as before \<close>
        then show ?thesis
          using 7 annots step_i_summarized_step_f_summarized.intros
          by meson
      qed
    qed
next
  case (8 f pre n ty p "is" t s)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (9 f fu pre n ty p "is" t s)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (10 f fu b s p uv pre n ty "is" t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (11 f fu b s p s' pre n ty "is" t)
  \<comment> \<open> our IH: it holds for the called function \<close>
  then have IH_f: "step_f_summarized\<^sup>*\<^sup>* (branchf s' None b f) errf"
    using mono_rtranclp
    by (metis (no_types, lifting))

  then show ?case
    \<comment> \<open> once again split based on whether we have annotations \<close>
    proof (cases "map_of annotations f = None")
      case True
      \<comment> \<open> if not - we can step to any next state including err \<close>
      then show ?thesis
        by (simp add: 11 step_i_summarized_step_f_summarized.intros)
    next
      case False
      \<comment> \<open> if we do, obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        by fast
      
      \<comment> \<open> and show this means we do not satisfy the precondition \<close>
      then have "\<not> fpre s'"
      proof -
        \<comment> \<open> if we did have the precond, then the weakest precondition over steps would hold by our vc  \<close>
        have "fpre s' \<Longrightarrow> wp_fs_with_summarization (branchf s' None b f) (\<lambda>s. fpost s' (state s) (ret_value s))"
          using assms 11 annots
          unfolding program_correct_with_summarization_def function_correct_with_summarization_def function_hoare_with_summarization_def
          by blast
        \<comment> \<open> however, that is a contradiction since wp specifies it does not reach errors \<close>
        then show ?thesis
          using IH_f function_state.disc(9) terminal_state_simps(4) wp_fs_with_summarization_def
          by blast
      qed

      \<comment> \<open> since we don't have the precondition, we can transition to any state including err \<close>
      then show ?thesis
        using 11 annots step_i_summarized_step_f_summarized.intros
        by meson
    qed
next
  case (12 f fu b s p s' s'' v' pre n ty "is" t)
 \<comment> \<open> our IH: it holds for the function we call \<close>
  then have IH_f: "step_f_summarized\<^sup>*\<^sup>* (branchf s' None b f) (retf s'' v' f)"
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
        using 12 step_i_summarized_step_f_summarized.intros
        by meson
    next
      case False
      \<comment> \<open> if we have annotations - obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        unfolding program_correct_with_summarization_def
        by fast

      then show ?thesis
      \<comment> \<open> depending on if the precondition holds at this point \<close>
      proof (cases "fpre s'")
        case True
       \<comment> \<open> the precondition holds, which means the pre/post pair holds (per the verification condition) \<close>
       then have "wp_fs_with_summarization (branchf s' None b f) (\<lambda>s. fpost s' (state s) (ret_value s))"
          using assms 12 annots
          unfolding program_correct_with_summarization_def function_correct_with_summarization_def function_hoare_with_summarization_def
          by blast

       \<comment> \<open> extract the postcondition \<close>
        hence post_holds: "fpost s' s'' v'"
          using IH_f
          unfolding wp_fs_with_summarization_def
          by force

        \<comment> \<open> and then we have our thesis - we have the postcondition just like in the replaced step relation \<close>
        then show ?thesis
          using 12 True annots step_i_summarized_step_f_summarized.intros
          by meson
      next
        case False
        \<comment> \<open> if not - we again do not know the next state so we can step to ANY state, safe for the same reason as before \<close>
        then show ?thesis
          using 12 annots step_i_summarized_step_f_summarized.intros
          by meson
      qed
    qed
next
  case (13 i s s' pre "is" t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (14 i s uw pre "is" t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (15 pre p s s' ps "is" t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (16 pre p s ux ps "is" t)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (17 f fu lab b prev s s' l)
  then show ?case
    using mono_rtranclp step_i_summarized_step_f_summarized.intros
    by (metis (no_types, lifting))
next
  case (18 f fu lab b prev s s' v)
  then show ?case
    using mono_rtranclp step_i_summarized_step_f_summarized.intros
    by (metis (no_types, lifting))
next
  case (19 f fu lab b prev s)
  then show ?case
    using mono_rtranclp step_i_summarized_step_f_summarized.intros
    by (metis (no_types, lifting))
next
  case (20 f fu lab s prev)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
next
  case (21 f s prev lab)
  then show ?case
    by (simp add: step_i_summarized_step_f_summarized.intros)
qed

lemma call_vc_impl_global_vc:
  "program_correct_with_summarization \<Longrightarrow> correctness_notion program annotations"
  
  unfolding program_correct_with_summarization_def correctness_notion_def
  unfolding function_correct_def function_correct_with_summarization_def
  unfolding function_hoare_def function_hoare_with_summarization_def
  unfolding wp_fs_def wp_fs_with_summarization_def
  using overapproximation
  by (smt (verit) function_correct_with_summarization_def function_hoare_with_summarization_def mono_rtranclp program_correct_with_summarization_def
      wp_fs_with_summarization_def)


lemma unfold_wp_f:
  assumes "map_of program f = Some fu"
  assumes "map_of (llvm_function.blocks fu) lab = Some b"
  assumes "wp_is_with_summarization
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
  shows "wp_f_with_summarization (branchf s prev lab f) Q"
  unfolding wp_f_with_summarization_def
  apply (intro allI impI)
  apply (cases rule: step_f_summarized.cases)
  using assms
  unfolding wp_is_with_summarization_def
  by auto

lemma unfold_wp_is:
  assumes "s \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> \<not>is_erri s \<and> Q s"
  assumes "\<not>s \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> wp_i_with_summarization s (\<lambda>s'. wp_is_with_summarization s' Q)"
  shows "wp_is_with_summarization s Q"
  unfolding wp_is_with_summarization_def
  apply (intro allI impI, elim conjE)
  subgoal for s'
    using assms apply (rotate_tac 0)
    apply (induction rule: converse_rtranclp_induct) apply blast
    unfolding wp_i_with_summarization_def
    by (smt (verit) step_i_summarized.simps terminal_state_simps(3) wp_is_with_summarization_def)
  done


named_theorems unfold_wp_i

lemma wp_step_i_br_label_intro[unfold_wp_i]:
  assumes "Q (flowi s (branch_label l))"
  shows "wp_i_with_summarization (execi pre ([],[],br_label l) s) Q"
  using assms
  unfolding wp_i_with_summarization_def
  apply (intro allI impI)
  using step_i_summarized.simps
  by simp

lemma wp_step_i_br_i1_intro[unfold_wp_i]:
  assumes "register_\<alpha> s b = Some (vi1 bool)"
  assumes "bool \<Longrightarrow> Q (flowi s (branch_label l1))"
  assumes "\<not>bool \<Longrightarrow> Q (flowi s (branch_label l2))"
  shows "wp_i_with_summarization (execi pre ([],[],br_i1 b l1 l2) s) Q"
  using assms
  unfolding wp_i_with_summarization_def
  apply (intro allI impI)
  using step_i_summarized.simps register_\<alpha>_eq_get_register
  by (cases bool; fastforce) \<comment> \<open> Takes a bit... \<close>

lemma wp_step_i_ret_None_intro[unfold_wp_i]:
  assumes "Q (flowi s (return_value None))"
  shows "wp_i_with_summarization (execi pre ([],[],ret None) s) Q"
  using assms
  unfolding wp_i_with_summarization_def
  apply (intro allI impI)
  using step_i_summarized.simps
  by simp

lemma wp_step_i_ret_value_intro[unfold_wp_i]:
  assumes "register_\<alpha> s v = Some v'"
  assumes "Q (flowi s (return_value (Some v')))"
  shows "wp_i_with_summarization (execi pre ([],[],ret (Some (t,v))) s) Q"
  using assms
  unfolding wp_i_with_summarization_def
  apply (intro allI impI)
  using step_i_summarized.simps register_\<alpha>_eq_get_register
  by simp

lemma wp_step_i_phi_intro[unfold_wp_i]:
  assumes "wp (execute_phi pre p s) (\<lambda>s'. Q (execi pre (ps,is,ter) s'))"
  shows "wp_i_with_summarization (execi pre (p#ps,is,ter) s) Q"
proof -
  obtain s' where "execute_phi pre p s = ok s'"
    using assms unfolding wp_def by (auto split: result.splits)
  then have "Q (execi pre (ps,is,ter) s')" using assms unfolding wp_def by simp
  then show ?thesis
    unfolding wp_i_with_summarization_def using step_i_summarized.simps \<open>execute_phi pre p s = ok s'\<close>
    by force
qed
lemma wp_step_i_instr_intro[unfold_wp_i]:
  assumes "is_call i \<Longrightarrow> i = call na ty f p"
  assumes "is_call i \<Longrightarrow> map_of program f = Some fu"
  assumes "is_call i \<Longrightarrow> first_label fu = Some b"
  assumes "is_call i \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)"
  assumes "is_call i \<Longrightarrow> wp (prepare_state s (params fu) p) (\<lambda>s'. fpre s' \<and> (\<forall>s'' v'. fpost s' s'' v' \<longrightarrow> wp (restore_state s s'' v' na) (\<lambda>s'''. Q (execi pre ([],is,ter) s''') )))"
  assumes "\<not>is_call i \<Longrightarrow> wp (execute_instruction i s) (\<lambda>s'. Q (execi pre ([],is,ter) s'))"
  shows "wp_i_with_summarization (execi pre ([],i#is,ter) s) Q"
  unfolding wp_i_with_summarization_def apply (intro allI impI) subgoal premises prems for si'
proof (cases "is_call i")
  case True

  have step: "step_i_summarized (execi pre ([],(call na ty f p)#is,ter) s) si'"
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
    apply (cases rule: step_i_summarized.cases; (simp del: split_paired_All))
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
    unfolding wp_i_with_summarization_def using step_i_summarized.simps \<open>execute_instruction i s = ok s'\<close> False prems
    by force \<comment> \<open> Takes a bit... \<close>
qed
  done

end

end
