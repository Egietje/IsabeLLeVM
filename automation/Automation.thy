theory Automation
  imports "../verification/FloydsMethod" "HOL-Eisbach.Eisbach" "../Word_Lib/Word_32" "../Word_Lib/Word_64" "../verification/InstructionTriples"
begin

section "Useful Shorthands"


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

lemma verify_program_impl_correctness_notion:
  assumes "verify_program program annotations"
  shows "correctness_notion program annotations"
  using assms verify_program_impl_floyd_vc floyd_vc_impl_global_vc
  by simp


abbreviation register_contains_value :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_value n v s \<equiv> register_\<alpha> s (reg n) = Some v"

abbreviation register_contains_allocated_address :: "llvm_identifier \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_allocated_address n s \<equiv> \<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> memory_\<alpha> s a \<noteq> None"

abbreviation register_contains_address_with_value :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_address_with_value n v s \<equiv> \<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> memory_\<alpha> s a = Some (mem_val v)"

fun unique_address :: "llvm_address \<Rightarrow> llvm_address list \<Rightarrow> bool" where
  "unique_address ad (a#as) = ((ad \<noteq> a) \<and> unique_address ad as)"
| "unique_address _ [] = True"

fun unique_addresses :: "llvm_address list \<Rightarrow> bool" where
  "unique_addresses (a#as) = (unique_address a as \<and> unique_addresses as)"
| "unique_addresses [] = True"

fun unique_addresses_rec :: "llvm_identifier list \<Rightarrow> state \<Rightarrow> llvm_address list \<Rightarrow> bool" where
  "unique_addresses_rec (n#ns) s as = (\<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> unique_addresses_rec ns s (a#as))"
| "unique_addresses_rec []     _ as = unique_addresses as"

fun registers_contain_unique_addresses :: "llvm_identifier list \<Rightarrow> state \<Rightarrow> bool" where
  "registers_contain_unique_addresses ns s = unique_addresses_rec ns s []"



section "Useful Lemmas"

lemma contract_updates:
  assumes "f s'' = (f s)(r1 := v1, r2 := v2) \<Longrightarrow> P"
  shows "f s' = (f s)(r1 := v1) \<Longrightarrow> f s'' = (f s')(r2 := v2) \<Longrightarrow> P"
  using assms
  by simp

lemma False_eq_False:
  assumes "False"
  shows "False"
  by (rule assms)



section "VCG Methods"


subsection "Clean Assumptions"

method repeat_minus_one methods m =
  ((m; succeeds m; repeat_minus_one m) | succeed)

method clean_registers = repeat_minus_one \<open>thin_tac "register_\<alpha> _ = _"\<close>
method clean_memory = repeat_minus_one \<open>thin_tac "memory_\<alpha> _ = _"\<close>

method clean_assms = ((elim exE conjE allE)+)?, (simp only: contract_updates)?; clean_registers?; clean_memory?; (simp only: triv_forall_equality)?
method clean_assms_non_destructive = ((elim exE conjE allE)+)?, (simp only: contract_updates)?; (simp only: triv_forall_equality)?

method unfold_unique_addresses = simp only: registers_contain_unique_addresses.simps unique_addresses.simps unique_addresses_rec.simps unique_address.simps HOL.simp_thms(21), clean_assms

subsection "Subgoal Solving Methods"

method sub_instantiate_register_address = rule asm_rl[of "register_\<alpha> _ _ = Some (addr _)"], (simp)?; fail
method sub_memory_valid = rule asm_rl[of "valid_memory_address _ _"], (simp)?; fail
method sub_register_value = rule asm_rl[of "register_\<alpha> _ _ = Some _"], (simp?; fastforce)?; fail
method sub_memory_value = rule asm_rl[of "memory_\<alpha> _ _ = Some (mem_val _)"], (simp split: if_splits)?; fail
method sub_add_poison = (rule asm_rl[of "add_no_poison32 _ _ _"] | rule asm_rl[of "add_no_poison64 _ _ _"]), (simp split: if_splits add: word_sless_alt word_sle_eq signed.leD)?; fail
method sub_icmp_same_signs = (rule asm_rl[of "if _ then same_signs32 _ _ else True"] | rule asm_rl[of "if _ then same_signs1 _ _ else True"] | rule asm_rl[of "if _ then same_signs64 _ _ else True"]), (simp split: if_splits add: word_sless_alt word_sle_eq)?; fail
method sub_map_of_some = rule asm_rl[of "map_of _ _ = Some _"], (simp)?; fail
method sub_distinct_first = rule asm_rl[of "distinct (map fst _)"], (simp)?; fail
method sub_some_refl = rule asm_rl[of "Some _ = Some _"], (rule refl)?; fail
method sub_is_lid = rule asm_rl[of "is_lid _"], (simp)?; fail
method sub_instantiate_phi = rule asm_rl[of "_ = phi _ _ _"], simp; fail

method solve_subgoal = sub_instantiate_register_address | sub_memory_valid | sub_register_value
                     | sub_memory_value | sub_add_poison | sub_icmp_same_signs | sub_map_of_some
                     | sub_distinct_first | sub_some_refl | sub_is_lid


subsection "Instruction Methods"

method strat_instr methods m = rule wp_rules, m, clean_assms

method strat_alloca = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr \<open>-\<close>
method strat_store  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr \<open>sub_instantiate_register_address, sub_register_value\<close>
method strat_load   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr \<open>sub_instantiate_register_address, sub_memory_value\<close>
method strat_add    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr \<open>sub_register_value, sub_register_value\<close>
method strat_icmp   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"],
  ((rule icmp1_triple, sub_register_value, sub_register_value)
  | (rule icmp32_triple, sub_register_value, sub_register_value)
  | (rule icmp64_triple, sub_register_value, sub_register_value)),
  clean_assms,
  simp only: compare_values_1.simps compare_values_32.simps compare_values_64.simps

method unfold_instr = rule asm_rl[of "wp (execute_instruction _ _) _"], rule wp_rules
                                                                                          
method vcg_instr = unfold_instr | strat_alloca | strat_store | strat_load | strat_add | strat_icmp


subsection "Phi Node Methods"

method strat_phi = rule asm_rl[of "wp (execute_phi _ _ _) _"], strat_instr \<open>sub_instantiate_phi, sub_some_refl, sub_map_of_some, sub_register_value\<close>








lemma register_\<alpha>_pop_contract [simp]:
  "register_\<alpha> (pop_frame s s') ref = (
     case ref of
       reg (lid n) \<Rightarrow> register_\<alpha> s (reg (lid n))
     | reg (gid n) \<Rightarrow> register_\<alpha> s' (reg (gid n))
     | val v       \<Rightarrow> Some v)"
  by (cases s; cases s'; cases ref; auto split: llvm_value_ref.splits llvm_identifier.splits) 
fun stack_len :: "state \<Rightarrow> nat" where
  "stack_len (lr, gr, sm, hm, gm) = length sm"

lemma memory_\<alpha>_pop_saddr [simp]:
  "memory_\<alpha> (pop_frame s s') (saddr a) = 
     (if memory_\<alpha> s (saddr a) \<noteq> None then memory_\<alpha> s' (saddr a) else None)"
  by (cases s; cases s'; simp add: single_memory_\<alpha>_def allocated_single_memory_address_def)

lemma memory_\<alpha>_pop_haddr [simp]:
  "memory_\<alpha> (pop_frame s s') (haddr a) = memory_\<alpha> s' (haddr a)"
  by (cases s; cases s'; simp)

lemma memory_\<alpha>_pop_gaddr [simp]:
  "memory_\<alpha> (pop_frame s s') (gaddr a) = memory_\<alpha> s' (gaddr a)"
  by (cases s; cases s'; simp)


lemma register_\<alpha>_push_frame [simp]:
  "register_\<alpha> (push_frame s) (reg (lid n)) = None"
  "register_\<alpha> (push_frame s) (reg (gid n)) = register_\<alpha> s (reg (gid n))"
  by (cases s; simp)+

lemma memory_\<alpha>_push_frame [simp]:
  "memory_\<alpha> (push_frame s) = memory_\<alpha> s"
  apply (rule ext) subgoal for ad
    by (cases s; cases ad; simp)
  done





lemma contract_updates_register[simp]:
  assumes trace_link: "\<And>r. register_\<alpha> callee_state (reg (gid r)) = f (reg (gid r))"
  assumes frame_invariant: "\<And>r name. r = reg (gid name) \<Longrightarrow> f r = register_\<alpha> caller_state r"
  shows "register_\<alpha> (pop_frame caller_state callee_state) = register_\<alpha> caller_state"
  apply (rule ext)
  subgoal for n apply (cases n)
  subgoal for name apply (cases name)
    using assms by (auto )
  by simp done

lemma pop_frame_peel_gaddr [simp]:
  "(\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then (C (gaddr ga \<mapsto> v)) a else None | _ \<Rightarrow> (C (gaddr ga \<mapsto> v)) a) =
   ((\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a) (gaddr ga \<mapsto> v))"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_peel_haddr [simp]:
  "(\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then (C (haddr ha \<mapsto> v)) a else None | _ \<Rightarrow> (C (haddr ha \<mapsto> v)) a) =
   ((\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a) (haddr ha \<mapsto> v))"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_peel_saddr [simp]:
  "(\<lambda>a. case a of saddr sa' \<Rightarrow> if M a \<noteq> None then (C (saddr sa \<mapsto> v)) a else None | _ \<Rightarrow> (C (saddr sa \<mapsto> v)) a) =
   (if M (saddr sa) \<noteq> None 
    then ((\<lambda>a. case a of saddr sa' \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a) (saddr sa \<mapsto> v))
    else (\<lambda>a. case a of saddr sa' \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a))"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_M_drop_saddr [simp]:
  "C (saddr sa') = None \<Longrightarrow>
   (\<lambda>a. case a of saddr sa \<Rightarrow> if (M(saddr sa' \<mapsto> v)) a \<noteq> None then C a else None | _ \<Rightarrow> C a) =
   (\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a)"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_peel_absolute_base [simp]:
  "(\<lambda>a. case a of saddr sa \<Rightarrow> if C a \<noteq> None then C a else None | _ \<Rightarrow> C a) = C"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma memory_pop_frame [simp]:
  assumes "memory_\<alpha> x = X"
  assumes "memory_\<alpha> y = Y"
  shows "memory_\<alpha> (pop_frame x y) = (\<lambda>a. case a of saddr sa \<Rightarrow> if X a \<noteq> None then Y a else None | _ \<Rightarrow> Y a)"
  apply (rule ext) subgoal for a using assms by (cases a) auto done

















method solve_subgoal_first_label uses func =
  (rule asm_rl[of "\<exists>y. (first_label _ = Some y)"] | rule asm_rl[of "first_label _ = Some _"]),
  (subst func)?,
  subst first_label_def,
  (simp; fail)
method solve_subgoal_map_of uses def =
  rule asm_rl[of "map_of _ _ = Some _"],
  (simp add: def; fail)
method solve_subgoal_register_value =
  rule asm_rl[of "register_contains_value _ _ _"],
  (simp; fail)
method solve_subgoal_var_is_Some =
  rule asm_rl[of "_ = Some _"],
  (simp; fail)

method vcg_assign_params =
  rule asm_rl[of "wp (assign_params (_#_) (_#_) _ _) _"],
  rule wp_assign_params_intro,
  solve_subgoal_register_value

method vcg_assign_params_empty =
  rule asm_rl[of "wp (assign_params [] [] _ _) _"],
  rule wp_assign_params_empty_intro

method vcg_prepare_state uses func =
  rule asm_rl[of "wp (prepare_state _ _ _) _"],
  simp only: prepare_state.simps,
  (subst func)?,
  simp (no_asm) del: assign_params.simps split_paired_All,
  (vcg_assign_params+)?,
  vcg_assign_params_empty,
  intro conjI[rotated],
  intro allI impI,
  elim exE conjE

method remove_invalid_premise =
  (match premises in "Some _ = None" \<Rightarrow> blast)

method vcg_set_register = 
  rule asm_rl[of "wp (set_register _ _ (pop_frame _ _)) _"],
  rule wp_rules, defer_tac 
method vcg_wp_ok =
  rule asm_rl[of "wp (ok _) _"],
  rule wp_rules

method clean_assms_after_call =
  elim conjE,
  simp,
  (hypsubst_thin)+,
  ((subst (asm) fun_upd_apply[symmetric])+)?,
  clean_assms,
  (thin_tac "register_\<alpha> _ (reg (gid _)) = register_\<alpha> _ (reg (gid _))")?

method vcg_restore_state =
  rule asm_rl[of "wp (restore_state _ _ _ _) _"],
  ((rule wp_restore_state_intro,
  solve_subgoal_var_is_Some); (simp; fail)?),
  (vcg_set_register | vcg_wp_ok);
  clean_assms_after_call?





method unfold_first_label uses func =
  subst first_label_def,
  (subst func)?,
  simp del: split_paired_All

method vcg_f uses prog func =
  rule asm_rl[of "wp_f_with_summarization _ _ _ _"],
  rule unfold_wp_f,
  (subst prog)?,
  simp,
  (subst func)?,
  simp?

method unfold_floyd_cond uses prog func =
  rule asm_rl[of "floyd_cond _ _ _ _ _ _ _"],
  subst floyd_cond_def,
  rule wp_annotated_step_intro,
  (vcg_f prog: prog func: func),
  clean_assms
  


method vcg_verify_program uses prog =
  rule asm_rl[of "verify_program _ _"],
  simp del: verify_function.simps,
  (subst prog)?,
  (simp del: verify_function.simps)?,
  (intro conjI)?


method vcg_i_phi =
  rule asm_rl[of "wp_i_with_summarization _ _ (execi _ (_#_,_,_) _) _"],
  intro unfold_wp_i;
  strat_phi

method vcg_i_instr =
  rule asm_rl[of "wp_i_with_summarization _ _ (execi _ ([],_#_,_) _) _"],
  intro unfold_wp_i;
  (simp; fail)?;
  (thin_tac "\<not>is_call _" | thin_tac "is_call _")?;
  vcg_instr+

method vcg_i_ter =
  rule asm_rl[of "wp_i_with_summarization _ _ (execi _ ([],[],_) _) _"],
  intro unfold_wp_i,
  (simp; fail)?

method vcg_i_call uses func prog annot =
  (rule asm_rl[of "wp_i_with_summarization _ _ (execi _ (_, (call _ _ _ _)#_, _) _) _"]),
  (intro unfold_wp_i; (simp; fail)?; (thin_tac "\<not>is_call _" | thin_tac "is_call _")?),
  solve_subgoal_map_of def: prog,
  solve_subgoal_first_label func: func,
  solve_subgoal_map_of def: annot,
  vcg_prepare_state func: func,
  vcg_restore_state

method vcg_is_execi uses block func prog annot =
  rule asm_rl[of "wp_is_with_summarization _ _ (execi _ _ _) _"],
  rule unfold_wp_is;
  (simp; fail)?;
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  (subst block)?,
  (vcg_i_call func: func prog: prog annot: annot | vcg_i_phi | vcg_i_instr | vcg_i_ter)

method vcg_is_branch uses block prog annot =
  rule asm_rl[of "wp_is_with_summarization _ _ (flowi _ (branch_label _)) _"],
  rule unfold_wp_is;
  ((simp only: terminal_state_simps; fail) | (simp; fail)?);
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  (simp (no_asm))?,
  rule wp_steps_until_intro;
  ((subst (asm) has_annotation_def, (subst (asm) prog)?, (subst (asm) annot)?, simp); fail)?,
  (thin_tac "has_annotation _ _ _" | thin_tac "\<not>has_annotation _ _ _")?

method vcg_is_return uses block prog annot =
  rule asm_rl[of "wp_is_with_summarization _ _ (flowi _ (return_value _)) _"],
  rule unfold_wp_is;
  (simp; fail)?;
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  simp (no_asm),
  rule wp_steps_until_intro;
  ((subst (asm) has_annotation_def, (subst (asm) prog)?, (subst (asm) annot)?, simp); fail)?,
  (thin_tac "has_annotation _ _ _" | thin_tac "\<not>has_annotation _ _ _")?

method vcg_is uses block prog annot func =
  vcg_is_execi block: block func: func prog: prog annot: annot |
  vcg_is_branch block: block prog: prog annot: annot |
  vcg_is_return block: block prog: prog annot: annot |
  vcg_f prog: prog func: func

method unfold_annotation_holds uses prog annot =
  (subst annotation_holds_def)?,
  (subst prog)?,
  (subst annot)?,
  (simp (no_asm) del: split_paired_All)?,
  (subst annot)?,
  (simp (no_asm) del: split_paired_All)?



method unfold_precond uses annot prog =
  (subst (asm) annotation_holds_def,
  (subst (asm) annot)?,
  (subst (asm) prog)?)?,
  (simp (no_asm_use) del: split_paired_All)?,
  clean_assms

method vcg_all_is uses blocks prog annot func =
  vcg_is block: blocks prog: prog annot: annot func: func;
  (vcg_all_is blocks: blocks prog: prog annot: annot func: func | succeed);
  (unfold_annotation_holds prog: prog annot: annot)?

method vcg_function uses annot prog func blocks =
  (rule asm_rl[of "verify_function _ _ _ _"],
  simp,
  (subst (3) annot)?,
  simp del: split_paired_All,
  (intro conjI, solve_subgoal_first_label func: func); unfold_first_label func: func;
  intro allI impI conjI; unfold_floyd_cond prog: prog func: func);
  (unfold_precond prog: prog annot: annot)?;
  vcg_all_is blocks: blocks prog: prog annot: annot func: func   
       
method vcg_program uses prog =
  (rule verify_program_impl_correctness_notion), vcg_verify_program prog: prog


method vcg uses annot prog func blocks =
  vcg_program prog: prog;
  vcg_function annot: annot prog: prog func: func blocks: blocks













section "Word Lemma Bundle"

bundle word_bundle
begin

lemma lt_imp_le: "(i::word32) <s 2 ^ 31 - 1 \<Longrightarrow> i \<le>s 2 ^ 31 - 2"
  by (simp add: word_sle_eq word_sless_alt)


lemma le_imp_lt: "i \<le>s 2 ^ 31 - 2 \<Longrightarrow> (i::word32) <s 2 ^ 31 - 1"
  by (simp add: word_sle_eq word_sless_alt)

lemma lt_inc_nlt_imp_eq[simp]: "(i::word32) <s (b::word32) \<Longrightarrow> \<not> i+1 <s b \<Longrightarrow> i+1 = b"
  apply (simp add: word_sle_eq word_sless_alt)
  by (smt (verit, ccfv_threshold) diff_add_cancel signed_arith_ineq_checks_to_eq_word32(1,2) signed_minus_1
      signed_take_bit_int_eq_self signed_take_bit_int_greater_eq_minus_exp sint_word_ariths(1,8) word_sint.Rep_eqD)

lemma lt_inc_nlt_mult_eq[simp]: "(i::word32) <s (b::word32) \<Longrightarrow> \<not> i+1 <s b \<Longrightarrow> a*i+a = a*b"
  by (metis (no_types, lifting) distrib_left lt_inc_nlt_imp_eq mult_numeral_1_right numeral_One)

lemma i_no_overflow_impl_positive[simp]: "0 \<le>s i \<Longrightarrow> (i::word32) <s 2^31 - 1 \<Longrightarrow> 0 \<le>s (i+1)"
  by (smt (verit, del_insts) add_diff_eq diff_add_cancel diff_numeral_special(10) of_int_eq_id signed_minus_1
      signed_take_bit_int_eq_self signed_take_bit_int_eq_self_iff signed_take_bit_int_greater_eq_minus_exp sint_word_ariths(1,2,8)
      word_sle_eq word_sless_alt)

lemma i_incr_no_overflow_impl_not_negative[simp]: "0 \<le>s (i::word32) \<Longrightarrow> (i::word32) <s 2^31 - 1 \<Longrightarrow> \<not> i + 1 <s 0"
  by (smt (verit, best) i_no_overflow_impl_positive word_sle_eq word_sless_alt)

lemma i_bounds_no_overflow_neg[simp]: "- (2 ^ 31) \<le> sint (a::word32) * sint (b::word32) \<Longrightarrow>
    sint a * sint b \<le> 2 ^ 31 - 1 \<Longrightarrow>
    0 \<le>s (i::word32) \<Longrightarrow>
    i <s b \<Longrightarrow>
    b \<le>s 2 ^ 31 - 1 \<Longrightarrow>
    i <s 2 ^ 31 - 1 \<Longrightarrow>
    a <s 0 \<Longrightarrow> a * i <s 0 \<Longrightarrow> \<not> 0 \<le>s a * i + a"
proof -
  assume bounds: "- (2^31) \<le> sint a * sint b" "sint a * sint b \<le> 2^31 - 1"
  assume hi: "0 \<le>s i" "i <s b" "b \<le>s 2^31 - 1" "i <s 2^31 - 1"
  assume neg: "a <s 0" "a * i <s 0"
  have sa: "sint a < 0"
    using neg(1) 
    by (simp add: word_sless_alt)
  have si: "0 \<le> sint i"
    using hi(1)
    by (simp add: word_sless_alt word_sle_eq)
  have si_lt: "sint i < 2^31 - 1"
    using hi(4) by (simp add: word_sless_alt word_sle_eq)
  have sb_lt: "sint b \<le> 2^31 - 1"
    using hi(3) by (simp add: word_sless_alt word_sle_eq)
  have sai_neg: "sint (a * i) < 0"
    using neg(2) by (simp add: word_sless_alt word_sle_eq)
  have no_ovf_ai: "sint (a * i) = sint a * sint i"
    using sai_neg sa si 
    apply(auto intro: signed_arith_sint simp: sint_word_ariths word_sless_alt word_sle_eq)
    by (smt (verit, del_insts) bounds(1) hi(2) mult_eq_0_iff mult_less_cancel_left_disj signed_take_bit_int_eq_self
        word_sless_alt)
  have no_ovf_sum: "sint (a * i + a) = sint (a * i) + sint a"
    proof -
      have lo: "-(2^31) \<le> sint (a * i) + sint a"
      proof -
        have si_lt_b: "sint i < sint b"
          using hi(2) by (simp add: word_sless_alt)
        have sb_bounds: "-(2^31) \<le> sint b"
          using si si_lt_b by auto
        have key: "sint a * sint b \<le> sint a * (sint i + 1)"
          using sa si_lt_b
          by (simp add: mult_le_cancel_left_neg)
        show ?thesis
          using no_ovf_ai key bounds(1) right_diff_distrib' mult_cancel_left2
          by (smt (verit) )
      qed
      have hi': "sint (a * i) + sint a \<le> 2^31 - 1"
        using sai_neg sa
        by simp
      then show ?thesis
        using lo hi' no_ovf_ai
        by (simp add: sint_word_ariths signed_take_bit_int_eq_self)
    qed
  show "\<not> 0 \<le>s a * i + a"
    unfolding word_sle_def
    using no_ovf_sum sai_neg sa
    by (smt (verit) neg(1) word_sle_def word_sle_eq word_sless_alt)
qed

lemma i_bounds_no_overflow_pos[simp]: "- (2 ^ 31) \<le> sint (a::word32) * sint (b::word32) \<Longrightarrow>
    sint a * sint b \<le> 2 ^ 31 - 1 \<Longrightarrow>
    0 <s b \<Longrightarrow>
    0 \<le>s (i::word32) \<Longrightarrow>
    i <s b \<Longrightarrow>
    b \<le>s 2 ^ 31 - 1 \<Longrightarrow>
    i <s 2 ^ 31 - 1 \<Longrightarrow>
    0 \<le>s a \<Longrightarrow> 0 \<le>s a * i \<Longrightarrow> \<not> a * i + a <s 0"
proof -
  assume bounds: "- (2^31) \<le> sint a * sint b" "sint a * sint b \<le> 2^31 - 1"
  assume hi: "0 \<le>s i" "i <s b" "b \<le>s 2^31 - 1" "i <s 2^31 - 1"
  assume pos: "0 \<le>s a" "0 \<le>s a * i"
  have sa: "sint a \<ge> 0"
    using pos(1)
    by (simp add: word_sle_eq)
  have si: "0 \<le> sint i"
    using hi(1)
    by (simp add: word_sless_alt word_sle_eq)
  have si_lt: "sint i < 2^31 - 1"
    using hi(4) by (simp add: word_sless_alt word_sle_eq)
  have sb_lt: "sint b \<le> 2^31 - 1"
    using hi(3) by (simp add: word_sless_alt word_sle_eq)
  have sai_neg: "sint (a * i) \<ge> 0"
    using pos(2) by (simp add: word_sless_alt word_sle_eq)
  have no_ovf_ai: "sint (a * i) = sint a * sint i"
    using sai_neg sa si 
    apply(auto intro: signed_arith_sint simp: sint_word_ariths word_sless_alt word_sle_eq)
    by (smt (verit, best) bounds(2) hi(2) mult_less_cancel_left_disj signed_take_bit_int_eq_self word_sless_alt
        zero_le_mult_iff)
  have no_ovf_sum: "sint (a * i + a) = sint (a * i) + sint a"
    proof -
      have lo: "-(2^31) \<le> sint (a * i) + sint a"
        using sa sai_neg by force
      have hi': "sint (a * i) + sint a \<le> 2^31 - 1"
      proof -
        have si_lt_b: "sint i < sint b"
          using hi(2) by (simp add: word_sless_alt)
        have sb_bounds: "-(2^31) \<le> sint b"
          using si si_lt_b by auto
        have key: "sint a * sint b \<ge> sint a * (sint i + 1)"
          using sa si_lt_b
          by (smt (verit, best) mult_less_cancel_left_disj)
        show ?thesis
          using no_ovf_ai key bounds(2) right_diff_distrib' mult_cancel_left2
          by (smt (verit, best))
      qed
      then show ?thesis
        using lo hi' no_ovf_ai
        by (simp add: sint_word_ariths signed_take_bit_int_eq_self)
    qed
  show ?thesis
    unfolding word_sle_def
    using no_ovf_sum sai_neg sa 
    by (smt (verit) pos(1) word_sle_def word_sle_eq word_sless_alt)
qed

lemma bounded_inc_no_overflow[simp]: "0 \<le>s i \<Longrightarrow> (b::word32) \<le>s 2^31-1 \<Longrightarrow> (i::word32) <s b \<Longrightarrow> 0 <s i+1"
  using sint_word_ariths word_sle_eq word_sless_alt add_diff_cancel_right' i_incr_no_overflow_impl_not_negative signed_0 signed_minus_1
  by (smt (verit, del_insts))
lemma pos_not_neg[simp]: "0 <s (i::word32)+1 \<Longrightarrow> \<not> i + 1 <s 0" by simp

end

end