theory EuclidProgram
  imports "VCG" "HOL.GCD"
begin


(*

int sub (int a, int b) {
    if (b == 0) {
      return a;
    } else {
      return sub(a, b + (-1)) + (-1);
    }
}

int rem (int a, int b) {
    if (a < b) {
        return a;
    } else {
        return rem(sub(a, b), b);
    }
}

int gcd(int a, int b) {
  if (b == 0) {
    return a;
  } else {
    return gcd(b, rem(a, b));
  }
}



define dso_local noundef i32 @sub(i32 noundef %a, i32 noundef %b) {
entry:
  %cmp = icmp eq i32 %b, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:
  br label %return

if.else:
  %add = add nsw i32 %b, -1
  %call = call noundef i32 @sub(i32 noundef %a, i32 noundef %add)
  %add1 = add nsw i32 %call, -1
  br label %return

return:
  %retval.0 = phi i32 [ %a, %if.then ], [ %add1, %if.else ]
  ret i32 %retval.0
}

define dso_local noundef i32 @rem(i32 noundef %a, i32 noundef %b) {
entry:
  %cmp = icmp slt i32 %a, %b
  br i1 %cmp, label %if.then, label %if.else

if.then:
  br label %return

if.else:
  %call = call noundef i32 @sub(i32 noundef %a, i32 noundef %b)
  %call1 = call noundef i32 @rem(i32 noundef %call, i32 noundef %b)
  br label %return

return:
  %retval.0 = phi i32 [ %a, %if.then ], [ %call1, %if.else ]
  ret i32 %retval.0
}

define dso_local noundef i32 @gcd(i32 noundef %a, i32 noundef %b) {
entry:
  %cmp = icmp eq i32 %b, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:
  br label %return

if.else:
  %call = call noundef i32 @rem(i32 noundef %a, i32 noundef %b)
  %call1 = call noundef i32 @gcd(i32 noundef %b, i32 noundef %call)
  br label %return

return:
  %retval.0 = phi i32 [ %a, %if.then ], [ %call1, %if.else ]
  ret i32 %retval.0
}

*)

abbreviation "sub_block_entry \<equiv>
  (
    [],
    [
      icmp (lid ''cmp'') False comp_eq i32 (reg (lid ''b'')) (val (vi32 0))
    ],
    br_i1 (reg (lid ''cmp'')) (lid ''if.then'') (lid ''if.else'')
  )"
abbreviation "sub_block_if \<equiv>
  (
    [],
    [],
    br_label (lid ''return'')
  )"

abbreviation "sub_block_else \<equiv>
  (
    [],
    [
      add (lid ''add'') add_nsw i32 (reg (lid ''b'')) (val (vi32 (-1))),
      call (Some (lid ''call'')) i32 (gid ''sub'') [(i32, reg (lid ''a'')),(i32, reg (lid ''add''))],
      add (lid ''add1'') add_nsw i32 (reg (lid ''call'')) (val (vi32 (-1)))
    ],
    br_label (lid ''return'')
  )
  "

abbreviation "sub_block_return \<equiv>
  (
    [
      phi (lid ''retval.0'') i32 [(lid ''if.then'', reg (lid ''a'')), (lid ''if.else'', reg (lid ''add1''))]
    ],
    [],
    ret (Some (i32, reg (lid ''retval.0'')))
  )
  "

abbreviation "sub_func \<equiv> func i32 [(lid ''a'', i32), (lid ''b'', i32)]
  [
    (lid ''entry'', sub_block_entry),
    (lid ''if.then'', sub_block_if),
    (lid ''if.else'', sub_block_else),
    (lid ''return'', sub_block_return)
  ]"


abbreviation "rem_block_entry \<equiv>
  (
    [],
    [
      icmp (lid ''cmp'') False comp_slt i32 (reg (lid ''a'')) (reg (lid ''b''))
    ],
    br_i1 (reg (lid ''cmp'')) (lid ''if.then'') (lid ''if.else'')
  )"
abbreviation "rem_block_if \<equiv>
  (
    [],
    [],
    br_label (lid ''return'')
  )"
abbreviation "rem_block_else \<equiv>
  (
    [],
    [
      call (Some (lid ''call'')) i32 (gid ''sub'') [(i32, reg (lid ''a'')),(i32, reg (lid ''b''))],
      call (Some (lid ''call1'')) i32 (gid ''rem'') [(i32, reg (lid ''call'')),(i32, reg (lid ''b''))]
    ],
    br_label (lid ''return'')
  )
  "
abbreviation "rem_block_return \<equiv>
  (
    [
      phi (lid ''retval.0'') i32 [(lid ''if.then'', reg (lid ''a'')), (lid ''if.else'', reg (lid ''call1''))]
    ],
    [],
    ret (Some (i32, reg (lid ''retval.0'')))
  )
  "

abbreviation "rem_func \<equiv> func i32 [(lid ''a'', i32), (lid ''b'', i32)]
  [
    (lid ''entry'', rem_block_entry),
    (lid ''if.then'', rem_block_if),
    (lid ''if.else'', rem_block_else),
    (lid ''return'', rem_block_return)
  ]"


abbreviation "gcd_block_entry \<equiv>
  (
    [],
    [
      icmp (lid ''cmp'') False comp_eq i32 (reg (lid ''b'')) (val (vi32 0))
    ],
    br_i1 (reg (lid ''cmp'')) (lid ''if.then'') (lid ''if.else'')
  )"
abbreviation "gcd_block_if \<equiv>
  (
    [],
    [],
    br_label (lid ''return'')
  )"
abbreviation "gcd_block_else \<equiv>
  (
    [],
    [
      call (Some (lid ''call'')) i32 (gid ''rem'') [(i32, reg (lid ''a'')),(i32, reg (lid ''b''))],
      call (Some (lid ''call1'')) i32 (gid ''gcd'') [(i32, reg (lid ''b'')),(i32, reg (lid ''call''))]
    ],
    br_label (lid ''return'')
  )
  "
abbreviation "gcd_block_return \<equiv>
  (
    [
      phi (lid ''retval.0'') i32 [(lid ''if.then'', reg (lid ''a'')), (lid ''if.else'', reg (lid ''call1''))]
    ],
    [],
    ret (Some (i32, reg (lid ''retval.0'')))
  )
  "

abbreviation "gcd_func \<equiv> func i32 [(lid ''a'', i32), (lid ''b'', i32)]
  [
    (lid ''entry'', gcd_block_entry),
    (lid ''if.then'', gcd_block_if),
    (lid ''if.else'', gcd_block_else),
    (lid ''return'', gcd_block_return)
  ]"

abbreviation euclid_prog :: llvm_program where "euclid_prog \<equiv> [(gid ''sub'', sub_func), (gid ''rem'', rem_func), (gid ''gcd'', gcd_func)]"

abbreviation "global_vars_equal s s' \<equiv> \<forall>n. register_\<alpha> s' (reg (gid n)) = register_\<alpha> s (reg (gid n))"

abbreviation "precond P s \<equiv> (\<exists>a b.
      register_\<alpha> s (reg (lid ''a'')) = Some (vi32 a)
    \<and> register_\<alpha> s (reg (lid ''b'')) = Some (vi32 b)
    \<and> P a b)"

abbreviation "postcond Q s s' v \<equiv> \<exists>a b r.
      register_\<alpha> s (reg (lid ''a'')) = Some (vi32 a)
    \<and> register_\<alpha> s (reg (lid ''b'')) = Some (vi32 b)
    \<and> memory_\<alpha> s = memory_\<alpha> s' \<and> global_vars_equal s s'
    \<and> v = Some (vi32 r) \<and> Q a b r"

abbreviation sub_annots :: "precondition * block_preconditions * postcondition" where
  "sub_annots \<equiv> (
    precond (\<lambda>a b. 0 \<le>s a \<and> 0 \<le>s b \<and> b \<le>s a),
    [],
    postcond (\<lambda>a b r. r = a - b)
  )"

abbreviation rem_annots :: "precondition * block_preconditions * postcondition" where
  "rem_annots \<equiv> (
    precond (\<lambda>a b. 0 \<le>s a \<and> 1 \<le>s b ),
    [],
    postcond (\<lambda>a b r. sint r = (sint a) mod (sint b))
  )"

abbreviation gcd_annots :: "precondition * block_preconditions * postcondition" where
  "gcd_annots \<equiv> (
    precond (\<lambda>a b. 0 \<le>s a \<and> 0 \<le>s b ),
    [],
    postcond (\<lambda>a b r. sint r = gcd (sint a) (sint b))
  )"


definition "euclid_annots \<equiv> [(gid ''sub'', sub_annots), (gid ''rem'', rem_annots), (gid ''gcd'', gcd_annots)]"


lemma "verify_program euclid_prog euclid_annots"
  apply vcg_verify_program
  subgoal (* sub function *)
    apply (vcg_verify_function annot: euclid_annots_def) 
    apply (all \<open>((simp add: word_sle_eq word_sless_eq; force); fail)?\<close>)
    subgoal
      by (simp add: word_sle_eq word_sless_eq, smt (verit, del_insts) More_Word.sint_0 diff_zero minus_diff_eq signed_arith_ineq_checks_to_eq_word32(1,2) signed_minus_1)
    subgoal
      by (simp add: word_sle_eq word_sless_eq, smt (verit, del_insts) diff_0_right eq_diff_eq signed_arith_ineq_checks_to_eq_word32(1,2) sint_minus1 uminus_add_conv_diff)
    done

  subgoal (* rem function *)
    apply (vcg_verify_function annot: euclid_annots_def) 
    apply (all \<open>((simp add: word_sle_eq word_sless_eq; force  ); fail)?\<close>)
    subgoal
      apply (simp add: word_sle_eq word_sless_eq)
      by (metis mod_pos_pos_trivial order_le_imp_less_or_eq word_sint.Rep_inverse)
    subgoal premises prems for s a b s'
    proof -
      have bleqa: "b \<le>s a" using prems 
        apply (simp add: word_sle_eq word_sless_eq)
        by auto
      then have "0 \<le>s a-b" using prems(3) prems(4) prems(5)
        apply (simp add: word_sle_eq word_sless_eq)
        by (smt (verit, ccfv_threshold) diff_0_right diff_right_commute diff_self minus_diff_eq signed_arith_eq_checks_to_ord(2) word_sle_eq)
      then have "sint (a-b) mod sint b = sint a mod sint b" using prems(3) prems(4) bleqa
        apply (simp add: word_sle_eq word_sless_eq) using prems(3)
        apply (simp only: word_sle_eq word_sless_eq)
        by (metis \<open>0 \<le>s a - b\<close> bleqa minus_mod_self2 signed_arith_eq_checks_to_ord(2))
      then show ?thesis using prems
        by (simp add: word_sle_eq word_sless_eq)
    qed
    subgoal
      apply (simp add: word_sle_eq word_sless_eq)
      by (smt (verit, ccfv_threshold) diff_right_commute diff_self eq_iff_diff_eq_0 signed_0 signed_arith_eq_checks_to_ord(2) word_sle_eq)
    done

  subgoal (* gcd function *)
    apply (vcg_verify_function annot: euclid_annots_def) 
    apply (all \<open>((simp add: word_sle_eq word_sless_eq; force); fail)?\<close>)
    subgoal
        apply (simp add: word_sle_eq word_sless_eq)
      using gcd_red_int by presburger
    subgoal 
      apply (simp add: word_sle_eq word_sless_eq)
      by (metis linorder_less_linear linorder_not_less mod_by_0 pos_mod_sign)
    subgoal
      apply (simp add: word_sle_eq word_sless_eq)
      by (meson int_one_le_iff_zero_less linorder_not_less signed_eq_0_iff verit_la_disequality)
    done
  done

end