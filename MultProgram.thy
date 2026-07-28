theory MultProgram
  imports "HOL-Library.AList_Mapping" "VCG"
begin


section "Mult Function"

definition mult_entry :: "llvm_instruction_block" where
  "mult_entry = (
    [],
    [
      alloca (lid ''a.addr'') i32 (Some 4),
      alloca (lid ''b.addr'') i32 (Some 4),
      alloca (lid ''result'') i32 (Some 4),
      alloca (lid ''i'') i32 (Some 4),
      store i32 (reg (lid ''a'')) (reg (lid ''a.addr'')) (Some 4),
      store i32 (reg (lid ''b'')) (reg (lid ''b.addr'')) (Some 4),
      store i32 (val (vi32 0)) (reg (lid ''result'')) (Some 4),
      store i32 (val (vi32 0)) (reg (lid ''i'')) (Some 4)
    ],
    br_label (lid ''for.cond'')
  )"


abbreviation mult_pre :: "precondition" where
  "mult_pre \<equiv> (\<lambda>s. \<exists>a b.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 b) s
  \<and> - (2 ^ 31) \<le> sint a * sint b
  \<and> sint a * sint b \<le> 2 ^ 31 - 1
  \<and> 0 <s b
  \<and> b \<le>s 2 ^ 31 - 1
  )"

(*
2 entry:
3 lid a.addr = alloca i32, align 4
4 lid b.addr = alloca i32, align 4
5 lid result = alloca i32, align 4
6 lid i = alloca i32, align 4
7 store i32 lid a, ptr lid a.addr, align 4
8 store i32 lid b, ptr lid b.addr, align 4
9 store i32 0, ptr lid result, align 4
10 store i32 0, ptr lid i, align 4
11 br label lid for.cond
*)


definition mult_cond :: "llvm_instruction_block" where
  "mult_cond = (
    [],
    [
      load (lid ''0'') i32 (reg (lid ''i'')) (Some 4),
      load (lid ''1'') i32 (reg (lid ''b.addr'')) (Some 4),
      icmp (lid ''cmp'') False comp_slt i32 (reg (lid ''0'')) (reg (lid ''1''))
    ],
    br_i1 (reg (lid ''cmp'')) (lid ''for.body'') (lid ''for.end'')
  )"

(*
13 for.cond:
14 lid 0 = load i32, ptr lid i, align 4
15 lid 1 = load i32, ptr lid b.addr, align 4
16 lid cmp = icmp slt i32 lid 0, lid 1
17 br i1 lid cmp, label lid for.body, label lid for.end
*)


definition mult_body :: "llvm_instruction_block" where
  "mult_body = (
    [],
    [
      load (lid ''2'') i32 (reg (lid ''a.addr'')) (Some 4),
      load (lid ''3'') i32 (reg (lid ''result'')) (Some 4),
      add (lid ''add'') add_nsw i32 (reg (lid ''3'')) (reg (lid ''2'')),
      store i32 (reg (lid ''add'')) (reg (lid ''result'')) (Some 4)
    ],
    br_label (lid ''for.inc'')
  )"

abbreviation mult_body_pre :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "mult_body_pre \<equiv> (\<lambda>s s'. \<exists>aa a ba b ia i resa.
    register_contains_value ((lid ''a.addr'')) (addr aa) s'
  \<and> register_contains_value ((lid ''i''))      (addr ia) s'
  \<and> register_contains_value ((lid ''b.addr'')) (addr ba) s'
  \<and> register_contains_value ((lid ''result'')) (addr resa) s'

  \<and> register_contains_value ((lid ''a'')) (vi32 a) s
  \<and> register_contains_value ((lid ''b'')) (vi32 b) s
  \<and> register_contains_value ((lid ''a'')) (vi32 a) s'
  \<and> register_contains_value ((lid ''b'')) (vi32 b) s'

  \<and> memory_\<alpha> s' = (memory_\<alpha> s)(
      aa   := Some (mem_val (vi32 a)),
      ba   := Some (mem_val (vi32 b)),
      ia   := Some (mem_val (vi32 i)),
      resa := Some (mem_val (vi32 (a*i)))
    )
  \<and> unique_addresses [aa, ba, ia, resa]
  \<and> 0 \<le>s i
  \<and> i <s b
  )"

(*
19 for.body:
20 lid 2 = load i32, ptr lid a.addr, align 4
21 lid 3 = load i32, ptr lid result, align 4
22 lid add = add nsw i32 lid 3, lid 2
23 store i32 lid add, ptr lid result, align 4
24 br label lid for.inc
*)


definition mult_inc :: "llvm_instruction_block" where
  "mult_inc = (
    [],
    [
      load (lid ''4'') i32 (reg (lid ''i'')) (Some 4),
      add (lid ''inc'') add_nsw i32 (reg (lid ''4'')) (val (vi32 1)),
      store i32 (reg (lid ''inc'')) (reg (lid ''i'')) (Some 4)
    ],
    br_label (lid ''for.cond'')
  )"


(*
26 for.inc:
27 lid 4 = load i32, ptr lid i, align 4
28 lid inc = add nsw i32 lid 4, 1
29 store i32 lid inc, ptr lid i, align 4
30 br label lid for.cond
*)


definition mult_end :: "llvm_instruction_block" where
  "mult_end = (
    [],
    [
      load (lid ''5'') i32 (reg (lid ''result'')) (Some 4)
    ],
    ret (Some (i32, (reg (lid ''5''))))
  )"

abbreviation mult_end_pre :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "mult_end_pre \<equiv> (\<lambda>s s'. \<exists>aa a ba b ia i resa.
    register_contains_value ((lid ''a.addr'')) (addr aa) s'
  \<and> register_contains_value ((lid ''i''))      (addr ia) s'
  \<and> register_contains_value ((lid ''b.addr'')) (addr ba) s'
  \<and> register_contains_value ((lid ''result'')) (addr resa) s'

  \<and> register_contains_value ((lid ''a'')) (vi32 a) s
  \<and> register_contains_value ((lid ''b'')) (vi32 b) s
  \<and> register_contains_value ((lid ''a'')) (vi32 a) s'
  \<and> register_contains_value ((lid ''b'')) (vi32 b) s'

  \<and> memory_\<alpha> s' = (memory_\<alpha> s)(
      aa   := Some (mem_val (vi32 a)),
      ba   := Some (mem_val (vi32 b)),
      ia   := Some (mem_val (vi32 i)),
      resa := Some (mem_val (vi32 (a*i)))
    )
  \<and> unique_addresses [aa, ba, ia, resa]
  \<and> i = b
  )"

abbreviation mult_post :: "postcondition" where
  "mult_post \<equiv> (\<lambda>s s' v. \<exists>a b i aa ba ia resa.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 b) s
  \<and> memory_\<alpha> s' = (memory_\<alpha> s)(
      aa   := Some (mem_val (vi32 a)),
      ba   := Some (mem_val (vi32 b)),
      ia   := Some (mem_val (vi32 i)),
      resa := Some (mem_val (vi32 (a*i)))
    )
  \<and> v = Some (vi32 (a * b))
  )"

(*
32 for.end:
33 lid 5 = load i32, ptr lid result, align 4
34 ret i32 lid 5
*)


definition mult_function :: llvm_function where
  "mult_function = (func i32
    [
      (lid ''a'', i32),
      (lid ''b'', i32)
    ]
    [
      (lid ''entry'',    mult_entry),
      (lid ''for.cond'', mult_cond),
      (lid ''for.body'', mult_body),
      (lid ''for.inc'',  mult_inc),
      (lid ''for.end'',  mult_end)
    ]
  )"

definition mult_program :: llvm_program where
  "mult_program \<equiv> [
    (gid ''mult'', mult_function)
  ]"
definition mult_annotations :: annotations where
  "mult_annotations \<equiv>
    [
      (gid ''mult'',
        (
          mult_pre,
          [
            ((lid ''for.cond'', lid ''for.body''), mult_body_pre),
            ((lid ''for.cond'', lid ''for.end'' ), mult_end_pre)
          ],
          mult_post
        )
      )
    ]"


lemma mult_floyd:
  "verify_program
    mult_program
    mult_annotations"
  including word_bundle
  apply (vcg_verify_program prog: mult_program_def)
  apply (vcg_verify_function blocks: mult_entry_def mult_cond_def mult_body_def mult_inc_def mult_end_def annot: mult_annotations_def prog: mult_program_def func: mult_function_def)

             apply (all \<open>((simp add: mult_program_def, force); fail)?\<close>)
  apply (auto split: if_splits simp: distrib_left)
  subgoal 
    apply (rule exI[where x="0"])
    by (auto simp: distrib_left)
  subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
    apply (rule exI[where x="i + 1"])
    by (auto simp: distrib_left)
  done


(*
1 define dso_local noundef i32 @mult(int, int)(i32 noundef lid a, i32 noundef lid b) { llvm
2 entry:
3 lid a.addr = alloca i32, align 4
4 lid b.addr = alloca i32, align 4
5 lid result = alloca i32, align 4
6 lid i = alloca i32, align 4
7 store i32 lid a, ptr lid a.addr, align 4
8 store i32 lid b, ptr lid b.addr, align 4
9 store i32 0, ptr lid result, align 4
10 store i32 0, ptr lid i, align 4
11 br label lid for.cond
12
13 for.cond:
14 lid 0 = load i32, ptr lid i, align 4
15 lid 1 = load i32, ptr lid b.addr, align 4
16 lid cmp = icmp slt i32 lid 0, lid 1
17 br i1 lid cmp, label lid for.body, label lid for.end
18
19 for.body:
20 lid 2 = load i32, ptr lid a.addr, align 4
21 lid 3 = load i32, ptr lid result, align 4
22 lid add = add nsw i32 lid 3, lid 2
23 store i32 lid add, ptr lid result, align 4
24 br label lid for.inc
25
26 for.inc:
27 lid 4 = load i32, ptr lid i, align 4
28 lid inc = add nsw i32 lid 4, 1
29 store i32 lid inc, ptr lid i, align 4
30 br label lid for.cond
31
32 for.end:
33 lid 5 = load i32, ptr lid result, align 4
34 ret i32 lid 5
35 }
*)


end