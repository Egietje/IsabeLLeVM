theory FloydsMethod
  imports FunctionSummarization
begin

context
  fixes program :: llvm_program
  fixes annotations :: annotations
begin


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
  "step_until fs fs' \<equiv> step_f_summarized program annotations fs fs' \<and> \<not>has_annotation fs"

definition annotated_step :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "s \<Rightarrow> s' \<equiv> (\<exists>x. step_f_summarized program annotations s x \<and> step_until\<^sup>*\<^sup>* x s') \<and> (has_annotation s' \<or> error_state s')"

abbreviation annotated_steps :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>*" 50) where
  "fs \<Rightarrow>* fs' \<equiv> annotated_step\<^sup>*\<^sup>* fs fs'"


definition wp_u where
  "wp_u fs Q \<equiv> (\<forall>fs'. step_until\<^sup>*\<^sup>* fs fs' \<and> \<not>error_state fs \<longrightarrow> \<not>error_state fs') \<and> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> has_annotation fs' \<longrightarrow> Q fs')"

definition wp_a where
  "wp_a fs Q \<equiv> (\<forall>fs'. ((fs \<Rightarrow> fs') \<longrightarrow> (\<not>error_state fs' \<and> Q fs')))"

definition "floyd_cond init s p l f \<equiv> wp_a (branchf s p l f) (\<lambda>fs'. annotation_holds init fs')"

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
  assumes "step_f_summarized program annotations fs x"
  assumes "step_until\<^sup>*\<^sup>* x fs'"
  assumes "has_annotation fs' \<or> error_state fs'"
  shows "fs \<Rightarrow> fs'"
  unfolding annotated_step_def
  using assms
  by blast


lemma wp_annotated_step_intro:
  assumes "wp_f_with_summarization program annotations fs (\<lambda>fs'. wp_u fs' Q)"
  shows "wp_a fs Q"
  using assms
  unfolding wp_a_def wp_f_with_summarization_def wp_u_def annotated_step_def
  by blast

lemma wp_steps_until_intro:
  assumes "has_annotation fs \<Longrightarrow> Q fs"
  assumes "\<not>has_annotation fs \<Longrightarrow> wp_f_with_summarization program annotations fs (\<lambda>fs'. wp_u fs' Q)"
  shows "wp_u fs Q"
  using assms
  unfolding wp_u_def wp_f_with_summarization_def
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
              unfolding wp_a_def annotation_holds_def
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
              using assms(2,3) prems(1) wp_a_def
              by blast
            done
          done
        qed
      done
    done
  subgoal for s v f 
    using assms
    unfolding annotated_step_def
    by (simp add: step_f_summarized.simps)
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
  assumes "n_rcf_steps program annotations n s s'"
  assumes "has_annotation s' \<or> error_state s'"
  shows "\<exists>x m. step_until\<^sup>*\<^sup>* s x \<and> (has_annotation x \<or> error_state x) \<and> n_rcf_steps program annotations m x s' \<and> m \<le> n"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain x where xdef: "n_rcf_steps program annotations n x s' \<and> step_f_summarized program annotations s x" by auto
  then show ?case
    by (metis converse_rtranclp_into_rtranclp le_refl less_Suc_eq_le nat_less_le
        rtranclp.rtrancl_refl step_until_def Suc)
qed


lemma steps_impl_annotated_steps:
  assumes "(step_f_summarized program annotations)\<^sup>*\<^sup>* sf sf'"
  assumes "has_annotation sf' \<or> error_state sf'"
  shows "sf \<Rightarrow>* sf'"
  using assms
proof -
  obtain n where ndef: "n_rcf_steps program annotations n sf sf'"
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
      
      obtain s1 where "step_f_summarized program annotations sf s1" and "n_rcf_steps program annotations nat s1 sf'"
        using less ndef Suc
        by auto

      then obtain s2 m where steps: "step_until\<^sup>*\<^sup>* s1 s2 \<and> (has_annotation s2 \<or> error_state s2) \<and> n_rcf_steps program annotations m s2 sf' \<and> m \<le> nat"
        using exists_first_cutpoint less assms
        by blast          
      then have "sf \<Rightarrow> s2"
        using \<open>step_f_summarized program annotations sf s1\<close> step_until_closure_to_annotated_step
        by blast
      then show ?thesis
        by (metis Suc steps converse_rtranclp_into_rtranclp less.IH less_Suc_eq_le)
    qed
  qed
qed

lemma annotated_step_keeps_function_ret:
  assumes "(step_f_summarized program annotations)\<^sup>*\<^sup>* sf (retf s' v f')"
  assumes "sf = (branchf s p l f)"
  shows "f' = f"
  using assms
  apply (induction arbitrary: s p l f rule: converse_rtranclp_induct) apply blast
  by (smt (verit) converse_rtranclpE function_state.distinct(1,6) function_state.inject(1)
      function_state.sel(7) step_f_summarized.simps
      terminal_state_simps(4,6))
  

lemma floyd_vc_impl_call_vc:
  assumes "floyd_vc"
  shows "program_correct_with_summarization program annotations"
  unfolding program_correct_with_summarization_def function_correct_with_summarization_def function_hoare_with_summarization_def wp_fs_with_summarization_def
  apply (intro allI impI) apply (rule conjI) defer
  subgoal for f
    using assms
    unfolding floyd_vc_def
    apply -
    apply (erule allE[where x=f])
    by (auto split: option.splits)
  apply (intro allI impI)
  apply (elim conjE)
  subgoal premises prems for f fu fpre bpres fpost l s s'
    proof -
      have rc_path: "(step_f_summarized program annotations)\<^sup>*\<^sup>* (branchf s None l f) s'"
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
      
      have annotated: "has_annotation s' \<or> error_state s'"
      proof (cases s')
        case (branchf x11 x12 x13 x14)
        then show ?thesis
          using s'_ter
          by force
      next
        case (retf state val func)
        obtain start where path: "(step_f_summarized program annotations)\<^sup>*\<^sup>* start s'" and startdef: "start \<noteq> retf state val func"
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
        by (metis FloydsMethod.annotated_step_keeps_function_ret Pair_inject option.inject prems(6) rc_path)
    qed
  done

end

lemma floyd_vc_impl_global_vc:
  "floyd_vc p a \<Longrightarrow> correctness_notion p a"
  using floyd_vc_impl_call_vc call_vc_impl_global_vc
  by blast

end
