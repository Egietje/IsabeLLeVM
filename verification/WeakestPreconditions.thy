theory WeakestPreconditions
  imports Correctness
begin

ML \<open>
val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>rearranged\<close>
      (Scan.lift (Parse.$$$ "(" |-- Parse.enum1 "," Parse.nat --| Parse.$$$ ")")
        >> (fn ps =>
              Thm.rule_attribute [] (fn _ => Drule.rearrange_prems ps)))
      "rearrange theorem premises");
\<close>

context
  fixes program :: "llvm_program"
  fixes annotations :: "annotations"
begin

section "Definitions"

definition wp_f where
  "wp_f fs Q \<equiv> (\<forall>fs'. step_f program fs fs' \<longrightarrow> \<not>error_state fs' \<and> Q fs')"

definition wp_is where
  "wp_is s Q \<equiv> (\<forall>s'. ((step_i program)\<^sup>*\<^sup>* s s' \<and> s' \<nexists>\<rightarrow>\<^sub>i) \<longrightarrow> (\<not>is_erri s' \<and> Q s'))"

definition wp_i where
  "wp_i s Q \<equiv> (\<forall>s'. (step_i program s s') \<longrightarrow> (\<not>is_erri s' \<and> Q s'))"

definition wp :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp m P = (case m of ok v \<Rightarrow> P v | err e \<Rightarrow> False)"




section "Monadic Programs"

named_theorems wp_rules

context
  notes wp_def[simp]
begin

subsection "Predicate Transformation Rules"

lemma wp_impl_ok[simp]:
  assumes "wp x Q"
  shows "\<exists>v. x = ok v"
  using assms
  by (cases x; simp)

lemma consequence:
  assumes "wp x Q"
  assumes "\<And>x. Q x \<Longrightarrow> Q' x"
  shows "wp x Q'"
  using assms
  by (simp split: result.splits)

lemma wp_ok[wp_rules, simp]:
  assumes "Q x"
  shows "wp (ok x) Q"
  using assms
  by simp

lemma wp_return:
  assumes "Q x"
  shows "wp (return x) Q"
  using assms
  by (simp add: return_def)

lemma wp_assert[wp_rules]:
  assumes "b \<Longrightarrow> wp f P"
  assumes "\<not>b \<Longrightarrow> False"
  shows "wp (do {assert e b; f}) P"
  using assms
  by (auto split: result.splits simp: bind_def) 
thm wp_assert

lemma wp_bind[wp_rules]:
  assumes "wp m (\<lambda>x. wp (f x) P)"
  shows "wp (do {x\<leftarrow>m; f x}) P"
  using assms
  by (cases m; simp add: bind_def)

lemma wp_case_option[wp_rules]:
  assumes "(c = None \<and> wp f P) \<or> (\<exists>v. c = Some v \<and> wp (g v) P)"
  shows "wp (case c of None \<Rightarrow> f | (Some v) \<Rightarrow> g v) P"
  using assms
  by auto

lemma wp_case_result[wp_rules]:
  assumes "(\<exists>e. c = err e \<and> wp (f e) P) \<or> (\<exists>v. c = ok v \<and> wp (g v) P)"
  shows "wp (case c of err e \<Rightarrow> f e | ok v \<Rightarrow> g v) P"
  using assms
  by auto

lemma wp_if[wp_rules]:
  assumes "b \<Longrightarrow> wp i Q"
  assumes "\<not>b \<Longrightarrow> wp e Q"
  shows "wp (if b then i else e) Q"
  using assms
  by auto

lemma wp_case_product[wp_rules]:
  assumes "\<And>b c. a = (b,c) \<Longrightarrow> wp (f b c) Q"
  shows "wp (case a of (b,c) \<Rightarrow> f b c) Q"
  using assms
  by (cases a; simp)

lemma wp_result:
  assumes "f = ok x" "Q x"
  shows "wp f Q"
  using assms
  by (cases f; simp)

end


named_theorems register_intro

lemma wp_set_single_register_lid_intro[THEN consequence, register_intro]:
  "wp (return (set_single_register n v lr,gr,sm,hm,gm)) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> (lr,gr,sm,hm,gm))(reg (lid n) := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> (lr,gr,sm,hm,gm))"
  unfolding set_single_register_def
  by (intro wp_rules wp_return; simp)
                                          
lemma wp_set_register_intro[THEN consequence, wp_rules]:
  assumes "is_lid n"
  shows "wp (set_register n v s) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  using assms
  by (cases n; cases s; simp; intro wp_rules register_intro; simp add: set_single_register_def)

lemma wp_get_register_intro[THEN consequence, rearranged (1,0), wp_rules]:
  assumes "register_\<alpha> s n \<noteq> None"
  shows "wp (get_register s n) (\<lambda>v'. register_\<alpha> s n = Some v')"
  using assms
  apply (cases s; cases n) subgoal for _ _ _ _ _ id by (cases id; simp; intro wp_rules; auto split: option.splits)
  by simp



lemma register_\<alpha>_eq[simp]: "register_\<alpha> (lr,gr,sm,hm,gm) = register_\<alpha> (lr,gr,sm',hm',gm')"
  apply (rule ext)
  subgoal for x
    apply (cases x; simp)
    subgoal for id
      by (cases id; simp)
    done
  done


named_theorems single_memory_simps
named_theorems single_memory_intro

lemma single_memory_\<alpha>_set[single_memory_simps]:
  assumes "valid_single_memory_address s a"
  shows "single_memory_\<alpha> (s[a := mem_val v]) = (single_memory_\<alpha> s)(a := Some (mem_val v))"
  using assms
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def valid_single_memory_address_def
  by (auto split: if_splits)

lemma memory_\<alpha>_set_stack[simp]:
  assumes "valid_memory_address (lr,gr,sm,hm,gm) (saddr a)"
  shows "memory_\<alpha> (lr,gr,sm[a := mem_val v],hm,gm) = ((memory_\<alpha> (lr,gr,sm,hm,gm))((saddr a) := Some (mem_val v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma memory_\<alpha>_set_heap[simp]:
  assumes "valid_memory_address (lr,gr,sm,hm,gm) (haddr a)"
  shows "memory_\<alpha> (lr,gr,sm,hm[a := mem_val v],gm) = ((memory_\<alpha> (lr,gr,sm,hm,gm))((haddr a) := Some (mem_val v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma memory_\<alpha>_set_global[simp]:
  assumes "valid_memory_address (lr,gr,sm,hm,gm) (gaddr a)"
  shows "memory_\<alpha> (lr,gr,sm,hm,gm[a := mem_val v]) = ((memory_\<alpha> (lr,gr,sm,hm,gm))((gaddr a) := Some (mem_val v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done


lemma single_memory_\<alpha>_allocate[single_memory_simps]:
  assumes "a \<noteq> length m"
  shows "single_memory_\<alpha> (m@[mem_unset]) a = (single_memory_\<alpha> m) a"
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
  using assms
  by (auto simp: nth_append)


lemma single_memory_\<alpha>_allocated[single_memory_simps]:
  "single_memory_\<alpha> (m@[mem_unset]) (length m) = Some mem_unset"
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
  by simp

lemma memory_\<alpha>_allocate_stack_eq:
  assumes "a \<noteq> (saddr (length sm))"
  shows "memory_\<alpha> (lr,gr,sm@[mem_unset],hm,gm) a = memory_\<alpha> (lr,gr,sm,hm,gm) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_heap_eq:
  assumes "a \<noteq> (haddr (length hm))"
  shows "memory_\<alpha> (lr,gr,sm,hm@[mem_unset],gm) a = memory_\<alpha> (lr,gr,sm,hm,gm) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_global_eq:
  assumes "a \<noteq> (gaddr (length gm))"
  shows "memory_\<alpha> (lr,gr,sm,hm,gm@[mem_unset]) a = memory_\<alpha> (lr,gr,sm,hm,gm) a"
  using assms
  by (cases a; simp add: single_memory_simps)


lemma memory_\<alpha>_allocate_stack[simp]:
  "memory_\<alpha> (lr,gr,sm@[mem_unset],hm,gm) = (memory_\<alpha> (lr,gr,sm,hm,gm))(saddr (length sm) := Some mem_unset)"
  by (auto simp: memory_\<alpha>_allocate_stack_eq single_memory_simps)

lemma memory_\<alpha>_allocate_heap[simp]:
  "memory_\<alpha> (lr,gr,sm,hm@[mem_unset],gm) = (memory_\<alpha> (lr,gr,sm,hm,gm))(haddr (length hm) := Some mem_unset)"
  by (auto simp: memory_\<alpha>_allocate_heap_eq single_memory_simps)

lemma memory_\<alpha>_allocate_global[simp]:
  "memory_\<alpha> (lr,gr,sm,hm,gm@[mem_unset]) = (memory_\<alpha> (lr,gr,sm,hm,gm))(gaddr (length gm) := Some mem_unset)"
  by (auto simp: memory_\<alpha>_allocate_global_eq single_memory_simps)


lemma single_memory_\<alpha>_free[single_memory_simps]:
  assumes "allocated_single_memory_address s a"
  shows "single_memory_\<alpha> (s[a := mem_freed]) = (single_memory_\<alpha> s)(a := Some mem_freed)"
  using assms
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
  by (auto split: if_splits)


lemma memory_\<alpha>_free_heap[simp]:
  assumes "allocated_memory_address (lr,gr,sm,hm,gm) (haddr a)"
  shows "memory_\<alpha> (lr,gr,sm,hm[a := mem_freed],gm) = (memory_\<alpha> (lr,gr,sm,hm,gm))(haddr a := Some mem_freed)"
  apply (rule ext)
  subgoal for a'
    using assms
    by (cases a'; simp add: single_memory_simps)
  done


lemma single_memory_\<alpha>_not_none_iff[single_memory_simps]:
  "allocated_single_memory_address s a \<longleftrightarrow> single_memory_\<alpha> s a \<noteq> None"
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by (cases "s!a"; simp)

lemma allocated_address_iff[simp]:
  "allocated_memory_address s a \<longleftrightarrow> memory_\<alpha> s a \<noteq> None"
  by (cases s; cases a; simp add: single_memory_simps)

lemma valid_address_iff[simp]:
  "valid_memory_address s a \<longleftrightarrow> (memory_\<alpha> s a \<noteq> None \<and> memory_\<alpha> s a \<noteq> Some mem_freed)"
  by (cases s; cases a; auto simp: single_memory_\<alpha>_def valid_single_memory_address_def)


lemma memory_\<alpha>_allocate_validity:
  assumes "memory_\<alpha> m' = (memory_\<alpha> m)(a := Some mem_unset)"
  shows "allocated_memory_address m' = (allocated_memory_address m)(a := True)" "valid_memory_address m' = (valid_memory_address m)(a := True)"
  using assms
  by (auto simp: fun_eq_iff)
  


lemma memory_\<alpha>_set_validity:
  assumes "valid_memory_address s a"
  assumes "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v))"
  shows "allocated_memory_address s' = allocated_memory_address s" "valid_memory_address s' = valid_memory_address s"
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr; cases "a = addr")
      by (auto simp add: single_memory_\<alpha>_def valid_single_memory_address_def)
  done
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr; cases "a = addr")
      by (auto simp add: single_memory_\<alpha>_def fun_upd_def valid_single_memory_address_def fun_eq_iff allocated_single_memory_address_def split: if_splits)
  done
  done

lemma memory_\<alpha>_free_validity:
  assumes "valid_memory_address s a"
  assumes "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_freed)"
  shows "allocated_memory_address s' = allocated_memory_address s" "valid_memory_address s' = (valid_memory_address s)(a := False)"
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr)
      by (auto simp: single_memory_\<alpha>_def valid_single_memory_address_def split: if_splits)
    done
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr; cases "a = addr")
      by (auto simp: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def fun_upd_def fun_eq_iff split: if_splits)
    done
  done


lemma memory_\<alpha>_distinct_addresses[simp]:
  "memory_\<alpha> s a1 = Some v \<Longrightarrow> memory_\<alpha> s a2 = None \<Longrightarrow> a1 \<noteq> a2"
  by auto




section "memory_\<alpha> operations"

lemma set_memory_\<alpha>:
  assumes "valid_memory_address s a"
  shows "\<exists>s'. set_memory a v s = ok s' \<and> memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v))"
  using assms
  by (cases s; cases a; auto simp: single_memory_\<alpha>_def set_single_memory_def valid_single_memory_address_def split: if_splits)

lemma allocate_stack_\<alpha>:
  assumes "allocate_stack s = (s', a)"
  shows "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_unset)"
  using assms
  by (cases s; cases s'; cases a; auto simp: allocate_stack_def allocate_single_memory_def)

lemma allocate_heap_\<alpha>:
  assumes "allocate_heap s = (s', a)"
  shows "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_unset)"
  using assms
  by (cases s; cases s'; cases a; auto simp: allocate_heap_def allocate_single_memory_def)

lemma allocate_global_\<alpha>:
  assumes "allocate_global s = (s', a)"
  shows "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_unset)"
  using assms
  by (cases s; cases s'; cases a; auto simp: allocate_global_def allocate_single_memory_def)

lemma free_memory_\<alpha>:
  assumes "valid_memory_address s (haddr a)"
  shows "\<exists>s'. free_memory (haddr a) s = ok s' \<and> memory_\<alpha> s' = (memory_\<alpha> s)((haddr a) := Some mem_freed)"
  using assms
  by (cases s; auto simp: single_memory_\<alpha>_def free_single_memory_def valid_single_memory_address_def split: if_splits)



section "Intro rules"

lemma wp_case_memory_value_intro[wp_rules]:
  assumes "x = mem_unset \<Longrightarrow> wp f Q"
  assumes "\<And>v. x = mem_val v \<Longrightarrow> wp (g v) Q"
  assumes "x = mem_freed \<Longrightarrow> wp h Q"
  shows "wp (case x of mem_unset \<Rightarrow> f | mem_val v \<Rightarrow> g v | mem_freed \<Rightarrow> h) Q"
  using assms
  by (cases x; simp)


lemma wp_get_single_memory_intro[THEN consequence, rotated -1, single_memory_intro]:
  assumes "valid_single_memory_address s a" "single_memory_\<alpha> s a \<noteq> Some mem_unset"
  shows "wp (get_single_memory s a) (\<lambda>x. single_memory_\<alpha> s a = Some (mem_val x))"
  using assms
  unfolding get_single_memory_def valid_single_memory_address_def single_memory_\<alpha>_def
  by (intro wp_rules; simp)

lemma wp_get_memory_intro[THEN consequence, rotated -1, wp_rules]:
  assumes "valid_memory_address s a" "memory_\<alpha> s a \<noteq> Some mem_unset"
  shows "wp (get_memory s a) (\<lambda>x. memory_\<alpha> s a = Some (mem_val x))"
  using assms
  by (cases a; cases s; simp; intro single_memory_intro; simp add: single_memory_\<alpha>_def valid_single_memory_address_def split: if_splits)


lemma wp_set_single_memory_intro[THEN consequence, rotated -1, single_memory_intro]:
  assumes "valid_single_memory_address s a"
  shows "wp (set_single_memory a v s) (\<lambda>s'. single_memory_\<alpha> s' = (single_memory_\<alpha> s)(a := Some (mem_val v)))"
  using assms
  unfolding set_single_memory_def
  by (intro wp_rules wp_return; simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def fun_eq_iff split: if_splits)


lemma wp_set_memory_intro[THEN consequence, rotated -1, wp_rules]:
  assumes "valid_memory_address s a"
  shows "wp (set_memory a v s) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v)) \<and> register_\<alpha> s = register_\<alpha> s')"
  using assms
  by (cases a; cases s; simp add: set_single_memory_def; intro wp_rules wp_return; simp; simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def fun_eq_iff split: if_splits)


lemma wp_free_single_memory_intro[THEN consequence, rotated -1, single_memory_intro]:
  assumes "valid_single_memory_address s a"
  shows "wp (free_single_memory a s) (\<lambda>s'. (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := Some mem_freed))"
  using assms
  unfolding free_single_memory_def
  apply (intro wp_rules wp_return)
  by (auto simp: single_memory_\<alpha>_free valid_single_memory_address_def)

lemma wp_free_memory_intro[THEN consequence, rotated -1, wp_rules]:
  assumes "valid_memory_address s (haddr a)"
  shows "wp (free_memory (haddr a) s) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)((haddr a) := Some mem_freed) \<and> register_\<alpha> s = register_\<alpha> s')"
  apply (cases s; simp)
  using assms
   apply (intro wp_rules single_memory_intro wp_return, auto) defer
  using assms valid_memory_address.simps apply blast
   apply (rule ext)
  subgoal for _ _ _ _ _ _ _ a' by (cases a'; simp)
  done


lemma wp_allocate_single_memory[THEN consequence, rotated -1, single_memory_intro]:
  "wp (return (allocate_single_memory s)) (\<lambda>(s', a). (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := Some mem_unset) \<and> single_memory_\<alpha> s a = None)"
  unfolding allocate_single_memory_def
  apply (intro wp_rules wp_return; auto simp: single_memory_simps)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)


lemma wp_allocate_stack_intro[THEN consequence, rotated -1, wp_rules]:
  "wp (return (allocate_stack s)) (\<lambda>(s', a). (\<exists>a'. a = saddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some mem_unset) \<and> memory_\<alpha> s a = None \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_stack_def allocate_single_memory_def
  apply (cases s; intro wp_rules wp_return; auto)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)

lemma wp_allocate_heap_intro[THEN consequence, rotated -1, wp_rules]:
  "wp (return (allocate_heap s)) (\<lambda>(s', a). (\<exists>a'. a = haddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some mem_unset) \<and> memory_\<alpha> s a = None \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_heap_def allocate_single_memory_def
  apply (cases s; intro wp_rules wp_return; auto)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)

lemma wp_allocate_global_intro[THEN consequence, rotated -1, wp_rules]:
  "wp (return (allocate_global s)) (\<lambda>(s', a). (\<exists>a'. a = gaddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some mem_unset) \<and> memory_\<alpha> s a = None \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_global_def allocate_single_memory_def
  apply (cases s; intro wp_rules wp_return; auto)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)


lemma wp_assign_params_intro:
  assumes "register_\<alpha> s v = Some va" 
  assumes "\<And>s''. register_\<alpha> s'' = (register_\<alpha> s')(reg n := Some va) \<Longrightarrow> memory_\<alpha> s'' = memory_\<alpha> s' \<Longrightarrow> wp (assign_params ps vs s s'') Q"
  assumes "is_lid n"
  shows "wp (assign_params ((n,t)#ps) ((t',v)#vs) s s') Q"
  apply simp apply (intro wp_rules) using assms by auto

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


section "Step Predicates"

lemma unfold_wp_f:
  assumes "map_of program f = Some fu"
  assumes "map_of (llvm_function.blocks fu) lab = Some b"
  assumes "wp_is
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
  shows "wp_f (branchf s prev lab f) Q"
  unfolding wp_f_def
  apply (intro allI impI)
  apply (cases rule: step_f.cases)
  using assms
  unfolding wp_is_def
  by auto

lemma unfold_wp_is:
  assumes "s \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> \<not>is_erri s \<and> Q s"
  assumes "\<not>s \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> wp_i s (\<lambda>s'. wp_is s' Q)"
  shows "wp_is s Q"
  unfolding wp_is_def
  apply (intro allI impI, elim conjE)
  subgoal for s'
    using assms apply (rotate_tac 0)
    apply (induction rule: converse_rtranclp_induct) apply blast
    unfolding wp_i_def
    by (smt (verit) step_i.simps terminal_state_simps(3) wp_is_def)
  done


named_theorems unfold_wp_i

lemma wp_step_i_br_label_intro[unfold_wp_i]:
  assumes "Q (flowi s (branch_label l))"
  shows "wp_i (execi pre ([],[],br_label l) s) Q"
  using assms
  unfolding wp_i_def
  apply (intro allI impI)
  using step_i.simps[of program]
  by simp
 

lemma wp_step_i_br_i1_intro[unfold_wp_i]:
  assumes "register_\<alpha> s b = Some (vi1 bool)"
  assumes "bool \<Longrightarrow> Q (flowi s (branch_label l1))"
  assumes "\<not>bool \<Longrightarrow> Q (flowi s (branch_label l2))"
  shows "wp_i (execi pre ([],[],br_i1 b l1 l2) s) Q"
  using assms
  unfolding wp_i_def
  apply (intro allI impI)
  using step_i.simps[of program] register_\<alpha>_eq_get_register
  by (cases bool; fastforce) \<comment> \<open> Takes a bit... \<close>

lemma wp_step_i_ret_None_intro[unfold_wp_i]:
  assumes "Q (flowi s (return_value None))"
  shows "wp_i (execi pre ([],[],ret None) s) Q"
  using assms
  unfolding wp_i_def
  apply (intro allI impI)
  using step_i.simps[of program]
  by simp

lemma wp_step_i_ret_value_intro[unfold_wp_i]:
  assumes "register_\<alpha> s v = Some v'"
  assumes "Q (flowi s (return_value (Some v')))"
  shows "wp_i (execi pre ([],[],ret (Some (t,v))) s) Q"
  using assms
  unfolding wp_i_def
  apply (intro allI impI)
  using step_i.simps[of program] register_\<alpha>_eq_get_register
  by simp

lemma wp_step_i_phi_intro[unfold_wp_i]:
  assumes "wp (execute_phi pre p s) (\<lambda>s'. Q (execi pre (ps,is,ter) s'))"
  shows "wp_i (execi pre (p#ps,is,ter) s) Q"
proof -
  obtain s' where "execute_phi pre p s = ok s'"
    using assms unfolding wp_def by (auto split: result.splits)
  then have "Q (execi pre (ps,is,ter) s')" using assms unfolding wp_def by simp
  then show ?thesis
    unfolding wp_i_def using step_i.simps[of program] \<open>execute_phi pre p s = ok s'\<close>
    by force
qed

end


end