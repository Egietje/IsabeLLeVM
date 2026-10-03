theory EvenOddProgram
  imports "../IsabeLLeVM"
begin

section "Even/odd Functions"

definition odd_entry :: "llvm_instruction_block" where
  "odd_entry \<equiv> (
    [],
    [
      alloca (lid ''n.addr'') i32 (Some 4),
      store i32 (reg (lid ''n'')) (reg (lid ''n.addr'')) (Some 4),
      load (lid ''0'') i32 (reg (lid ''n.addr'')) (Some 4),
      call (Some (lid ''call'')) i1 (gid ''even'') [(i32, reg (lid ''0''))],
      icmp (lid ''lnot'') False comp_eq i1 (reg (lid ''call'')) (val (vi1 False))
    ],
    ret (Some (i1, (reg (lid ''lnot''))))
  )"

definition odd_func :: "llvm_function" where
  "odd_func \<equiv> func i1 [(lid ''n'', i32)]
    [
      (lid ''entry'', odd_entry)
    ]"


definition even_entry :: "llvm_instruction_block" where
  "even_entry \<equiv> (
    [],
    [
      alloca (lid ''retval'') i1 (Some 1),
      alloca (lid ''n.addr'') i32 (Some 4),
      store i32 (reg (lid ''n'')) (reg (lid ''n.addr'')) (Some 4),
      load (lid ''0'') i32 (reg (lid ''n.addr'')) (Some 4),
      icmp (lid ''cmp'') False comp_eq i32 (reg (lid ''0'')) (val (vi32 0))
    ],
    br_i1 (reg (lid ''cmp'')) (lid ''if.then'') (lid ''if.else'')
  )"
definition even_if :: "llvm_instruction_block" where
  "even_if \<equiv> (
    [],
    [
      store i1 (val (vi1 True)) (reg (lid ''retval'')) (Some 1)
    ],
    br_label (lid ''return'')
  )"
definition even_else :: "llvm_instruction_block" where
  "even_else \<equiv> (
    [],
    [
      load (lid ''1'') i32 (reg (lid ''n.addr'')) (Some 4),
      add (lid ''sub'') add_nsw i32 (reg (lid ''1'')) (val (vi32 (-1))),
      call (Some (lid ''call'')) i1 (gid ''odd'') [(i32, reg (lid ''sub''))],
      store i1 (reg (lid ''call'')) (reg (lid ''retval'')) (Some 1)
    ],
    br_label (lid ''return'')
  )"
definition even_return :: "llvm_instruction_block" where
  "even_return \<equiv> (
    [],
    [
      load (lid ''2'') i32 (reg (lid ''retval'')) (Some 4)
    ],
    ret (Some (i1, (reg (lid ''2''))))
  )"

definition even_func :: "llvm_function" where
  "even_func \<equiv> func i1 [(lid ''n'', i32)]
    [
      (lid ''entry'', even_entry),
      (lid ''if.then'', even_if),
      (lid ''if.else'', even_else),
      (lid ''return'', even_return)
    ]"

abbreviation even_annots :: "precondition * block_preconditions * postcondition" where
  "even_annots \<equiv> (
    (\<lambda>s.
      \<exists>n. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> 0 \<le>s n
    ),
    [],
    (\<lambda>s s' v.
      \<exists>n b a1 a2. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> v = Some (vi1 (even n))
    \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr a1 := Some (mem_val (vi32 n)), saddr a2 := Some (mem_val (vi1 b)))
    \<and> memory_\<alpha> s (saddr a1) = None
    \<and> memory_\<alpha> s (saddr a2) = None
    \<and> (\<forall>n. register_\<alpha> s' (reg (gid n)) = register_\<alpha> s (reg (gid n)))
    )
  )"
abbreviation odd_annots :: "precondition * block_preconditions * postcondition" where
  "odd_annots \<equiv> (
    (\<lambda>s.
      \<exists>n. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> 0 \<le>s n
    ),
    [],
    (\<lambda>s s' v.
      \<exists>n ad. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> v = Some (vi1 (odd n))
    \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr ad := Some (mem_val (vi32 n)))
    \<and> memory_\<alpha> s (saddr ad) = None
    \<and> (\<forall>n. register_\<alpha> s' (reg (gid n)) = register_\<alpha> s (reg (gid n)))
    )
  )"

definition even_odd_prog :: "llvm_program" where
  "even_odd_prog \<equiv> [
    (gid ''even'', even_func),
    (gid ''odd'',  odd_func)
  ]"

definition even_odd_annots :: "annotations" where
  "even_odd_annots \<equiv> [
    (gid ''even'', even_annots),
    (gid ''odd'',  odd_annots)
  ]"







lemma even_odd_correct:
  "correctness_notion even_odd_prog even_odd_annots"
  apply (vcg_program prog: even_odd_prog_def)

  subgoal (* even function *)
    apply (vcg_function blocks: even_entry_def even_if_def even_else_def even_return_def prog: even_odd_prog_def annot: even_odd_annots_def func: even_func_def odd_func_def)
    apply (all \<open>((intro conjI)?; ((simp; fail)?))\<close>)
    apply (auto split: if_splits simp: even_odd_prog_def)
    apply (smt (verit, del_insts) add.inverse_neutral add_diff_cancel_right' diff_minus_eq_add fun_upd_same signed.nle_le signed_arith_eq_checks_to_ord(1) signed_minus_1
          word_sle_eq)
    by (simp add: word_sless_alt word_sle_eq signed.leD)
  subgoal (* odd function *)
    apply (vcg_function blocks: odd_entry_def prog: even_odd_prog_def annot: even_odd_annots_def func: even_func_def odd_func_def)
    unfolding even_odd_prog_def
    by (auto split: if_splits)
  done

(*
define dso_local noundef zeroext i1 @odd(int)(i32 noundef lid n) {
entry:
  lid n.addr = alloca i32, align 4
  store i32 lid n, ptr lid n.addr, align 4
  lid 0 = load i32, ptr lid n.addr, align 4
  lid sub = sub nsw i32 lid 0, 1
  lid call = call noundef zeroext i1 @even(int)(i32 noundef lid sub)
  lid lnot = xor i1 lid call, true
  ret i1 lid lnot
}

define dso_local noundef zeroext i1 @even(int)(i32 noundef lid n) {
entry:
  lid retval = alloca i1, align 1
  lid n.addr = alloca i32, align 4
  store i32 lid n, ptr lid n.addr, align 4
  lid 0 = load i32, ptr lid n.addr, align 4
  lid cmp = icmp eq i32 lid 0, 0
  br i1 lid cmp, label lid if.then, label lid if.else

if.then:
  store i1 true, ptr lid retval, align 1
  br label lid return

if.else:
  lid 1 = load i32, ptr lid n.addr, align 4
  lid call = call noundef zeroext i1 @odd(int)(i32 noundef lid 1)
  lid lnot = xor i1 lid call, true
  store i1 lid lnot, ptr lid retval, align 1
  br label lid return

return:
  lid 2 = load i1, ptr lid retval, align 1
  ret i1 lid 2
}




bool even(int n);

/*@
assumes n \<ge> 0;
asserts \result = odd n;
asserts \<exists>a1 n. \resmem = (\inimem)(stack a1 \<mapsto> int n);
asserts \resglo = \iniglo
*/
bool odd(int n) {
    return !even(n);
}

/*@
assumes n \<ge> 0;
asserts \result = even n;
asserts \resmem = (\inimem)(stack a1 \<mapsto> int n, stack a2 \<mapsto> bool b);
asserts \resglo = \iniglo
*/
bool even(int n) {
    if (n == 0) {
        return true;
    } else {
        return odd(n-1);
    }
}



abbreviation even_annots :: "precondition * block_preconditions * postcondition" where
  "even_annots \<equiv> (
    (\<lambda>s.
      \<exists>n. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> 0 \<le>s n
    ),
    [],
    (\<lambda>s s' v.
      \<exists>n b a1 a2. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> v = Some (vi1 (even n))
    \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr a1 := Some (mem_val (vi32 n)), saddr a2 := Some (mem_val (vi1 b)))
    \<and> memory_\<alpha> s (saddr a1) = None
    \<and> memory_\<alpha> s (saddr a2) = None
    \<and> (\<forall>n. register_\<alpha> s' (reg @n) = register_\<alpha> s (reg @n))
    )
  )"
abbreviation odd_annots :: "precondition * block_preconditions * postcondition" where
  "odd_annots \<equiv> (
    (\<lambda>s.
      \<exists>n. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> 0 \<le>s n
    ),
    [],
    (\<lambda>s s' v.
      \<exists>n ad. register_\<alpha> s (reg (lid ''n'')) = Some (vi32 n)
    \<and> v = Some (vi1 (odd n))
    \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr ad := Some (mem_val (vi32 n)))
    \<and> memory_\<alpha> s (saddr ad) = None
    \<and> (\<forall>n. register_\<alpha> s' (reg @n) = register_\<alpha> s (reg @n))
    )
  )"

*)

















end