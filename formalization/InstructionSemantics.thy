theory InstructionSemantics
  imports StateModel
begin

section "Memory instructions"

fun get_address_from_pointer :: "state \<Rightarrow> llvm_pointer \<Rightarrow> llvm_address result" where
  "get_address_from_pointer s p = do {
    a \<leftarrow> get_register s p;
    (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address)
  }"


definition execute_alloca :: "llvm_identifier \<Rightarrow> state \<Rightarrow> state result" where
  "execute_alloca name s = do {
      (s', a) \<leftarrow> return (allocate_stack s);
      set_register name (addr a) s'
    }"

definition execute_store :: "llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> state \<Rightarrow> state result" where
  "execute_store v p s = do {
    address \<leftarrow> get_address_from_pointer s p;
    value \<leftarrow> get_register s v;
    set_memory address value s
  }"

definition execute_load :: "llvm_identifier \<Rightarrow> llvm_pointer \<Rightarrow> state \<Rightarrow> state result" where
  "execute_load n p s = do {
    a \<leftarrow> get_address_from_pointer s p;
    v \<leftarrow> get_memory s a;
    set_register n v s
  }"


section "Add instruction"

fun unsigned_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "unsigned_overflow32 a b = (a + b < a)"

(* a and b are negative \<longrightarrow> a + b must be negative *)
(* a and b are positive \<longrightarrow> a + b must be positive *)
(* a and b are different \<longrightarrow> a + b cannot overflow*)
fun signed_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "signed_overflow32 a b = ((a <s 0 \<and> b <s 0 \<and> 0 \<le>s a+b) \<or> (0 \<le>s a \<and> 0 \<le>s b \<and> a+b <s 0))"

fun unsigned_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "unsigned_overflow64 a b = (a + b < a)"

fun signed_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "signed_overflow64 a b = ((a <s 0 \<and> b <s 0 \<and> 0 \<le>s a+b) \<or> (0 \<le>s a \<and> 0 \<le>s b \<and> a+b <s 0))"

definition add_no_poison32 :: "llvm_add_wrap \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "add_no_poison32 wrap a b = (
      let uov = unsigned_overflow32 a b;
          sov = signed_overflow32 a b
      in case wrap of
           add_default \<Rightarrow> True
         | add_nuw \<Rightarrow> \<not>uov
         | add_nsw \<Rightarrow> \<not>sov
         | add_nuw_nsw \<Rightarrow> \<not>uov \<and> \<not>sov
     )"

declare add_no_poison32_def[simp]

definition add_no_poison64 :: "llvm_add_wrap \<Rightarrow> word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "add_no_poison64 wrap a b = (
      let uov = unsigned_overflow64 a b;
          sov = signed_overflow64 a b
      in case wrap of
           add_default \<Rightarrow> True
         | add_nuw \<Rightarrow> \<not>uov
         | add_nsw \<Rightarrow> \<not>sov
         | add_nuw_nsw \<Rightarrow> \<not>uov \<and> \<not>sov
     )"

declare add_no_poison64_def[simp]

fun add_values :: "llvm_add_wrap \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "add_values wrap (vi32 a) (vi32 b) = (if add_no_poison32 wrap a b then ok (vi32 (a+b)) else ok poison)"
| "add_values wrap (vi64 a) (vi64 b) = (if add_no_poison64 wrap a b then ok (vi64 (a+b)) else ok poison)"
| "add_values _ poison (vi32 _) = ok poison"
| "add_values _ (vi32 _) poison = ok poison"
| "add_values _ poison (vi64 _) = ok poison"
| "add_values _ (vi64 _) poison = ok poison"
| "add_values _ poison poison = ok poison"
| "add_values _ _ _ = err incompatible_types"


definition execute_add :: "llvm_identifier \<Rightarrow> llvm_add_wrap \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state \<Rightarrow> state result" where
  "execute_add name wrap v1 v2 s = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> add_values wrap v1' v2';
    set_register name res s
  }"

section "Compare instruction"

fun compare_values_1 :: "llvm_compare_condition \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> llvm_value" where
  "compare_values_1 comp_eq  a b = vi1 (a = b)"
| "compare_values_1 comp_ne  a b = vi1 (a \<noteq> b)"
| "compare_values_1 comp_ugt a b = vi1 (a \<and> (\<not>b))"
| "compare_values_1 comp_uge a b = vi1 (a \<or> (\<not>b))"
| "compare_values_1 comp_ult a b = vi1 ((\<not>a) \<and> b)"
| "compare_values_1 comp_ule a b = vi1 ((\<not>a) \<or> b)"
| "compare_values_1 comp_sgt a b = vi1 ((\<not>a) \<and> b)"
| "compare_values_1 comp_sge a b = vi1 ((\<not>a) \<or> b)"
| "compare_values_1 comp_slt a b = vi1 (a \<and> (\<not>b))"
| "compare_values_1 comp_sle a b = vi1 (a \<or> (\<not>b))"

fun compare_values_32 :: "llvm_compare_condition \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> llvm_value" where
  "compare_values_32 comp_eq a b = vi1 (a = b)"
| "compare_values_32 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_32 comp_ugt a b = vi1 (a > b)"
| "compare_values_32 comp_uge a b = vi1 (a \<ge> b)"
| "compare_values_32 comp_ult a b = vi1 (a < b)"
| "compare_values_32 comp_ule a b = vi1 (a \<le> b)"
| "compare_values_32 comp_sgt a b = vi1 (b <s a)"
| "compare_values_32 comp_sge a b = vi1 (b \<le>s a)"
| "compare_values_32 comp_slt a b = vi1 (a <s b)"
| "compare_values_32 comp_sle a b = vi1 (a \<le>s b)"

fun compare_values_64 :: "llvm_compare_condition \<Rightarrow> word64 \<Rightarrow> word64 \<Rightarrow> llvm_value" where
  "compare_values_64 comp_eq a b = vi1 (a = b)"
| "compare_values_64 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_64 comp_ugt a b = vi1 (a > b)"
| "compare_values_64 comp_uge a b = vi1 (a \<ge> b)"
| "compare_values_64 comp_ult a b = vi1 (a < b)"
| "compare_values_64 comp_ule a b = vi1 (a \<le> b)"
| "compare_values_64 comp_sgt a b = vi1 (b <s a)"
| "compare_values_64 comp_sge a b = vi1 (b \<le>s a)"
| "compare_values_64 comp_slt a b = vi1 (a <s b)"
| "compare_values_64 comp_sle a b = vi1 (a \<le>s b)"

fun compare_values :: "llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values c (vi1  a) (vi1  b) = ok (compare_values_1  c a b)"
| "compare_values c (vi32 a) (vi32 b) = ok (compare_values_32 c a b)"
| "compare_values c (vi64 a) (vi64 b) = ok (compare_values_64 c a b)"
| "compare_values _ _ _ = err incompatible_types"

fun same_signs1 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "same_signs1 a b = (a = b)"
fun same_signs32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "same_signs32 a b = ((a <s 0 \<and> b <s 0) \<or> (0 \<le>s a \<and> 0 \<le>s b))"
fun same_signs64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "same_signs64 a b = ((a <s 0 \<and> b <s 0) \<or> (0 \<le>s a \<and> 0 \<le>s b))"

fun compare_values_sign :: "llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values_sign False c a b = compare_values c a b"
| "compare_values_sign True c (vi1  a) (vi1  b) = (if same_signs1  a b then compare_values c (vi1  a) (vi1  b) else ok poison)"
| "compare_values_sign True c (vi32 a) (vi32 b) = (if same_signs32 a b then compare_values c (vi32 a) (vi32 b) else ok poison)"
| "compare_values_sign True c (vi64 a) (vi64 b) = (if same_signs64 a b then compare_values c (vi64 a) (vi64 b) else ok poison)"
| "compare_values_sign True c _ _ = err incompatible_types"


definition execute_icmp :: "llvm_identifier \<Rightarrow> llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state \<Rightarrow> state result" where
  "execute_icmp name same_sign cond v1 v2 s = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> compare_values_sign same_sign cond v1' v2';
    set_register name res s
  }"


section "Instruction wrapper"

fun execute_instruction :: "llvm_instruction \<Rightarrow> state \<Rightarrow> state result" where
  (* Allocate new memory value on the stack, and set the specified register to its address. *)
  "execute_instruction (alloca name type align) s = execute_alloca name s"
  (* Read address from pointer and store value in the stack or the heap. *)
| "execute_instruction (store type value pointer align) s = execute_store value pointer s"
  (* Read address from pointer and load value from either the stack or the heap. *)
| "execute_instruction (load name type pointer align) s = execute_load name pointer s"
  (* Get values, add according to wrap option (or poison), and store in register. *)
| "execute_instruction (add name wrap type v1 v2) s = execute_add name wrap v1 v2 s"
  (* Get values, do comparison, and store in register. *)
| "execute_instruction (icmp name same_sign cond type v1 v2) s = execute_icmp name same_sign cond v1 v2 s"
| "execute_instruction (call name type fun param) s = err internal_error"



section "Phi instruction"

fun phi_lookup :: "llvm_identifier option \<Rightarrow> (llvm_identifier * llvm_value_ref) list \<Rightarrow> llvm_value_ref result" where
  "phi_lookup l ls = do {
    prev \<leftarrow> (case l of Some v \<Rightarrow> ok v | None \<Rightarrow> err phi_no_previous_block);
    assert phi_label_not_distinct (distinct (map fst ls));
    case (map_of ls prev) of Some v \<Rightarrow> ok v | None \<Rightarrow> err phi_label_not_found
  }"


definition execute_phi :: "llvm_identifier option \<Rightarrow> llvm_phi_node \<Rightarrow> state \<Rightarrow> state result" where
  "execute_phi prev p s = (case p of phi name type values \<Rightarrow> do {
    v \<leftarrow> phi_lookup prev values;
    v' \<leftarrow> get_register s v;
    set_register name v' s
  })"


end