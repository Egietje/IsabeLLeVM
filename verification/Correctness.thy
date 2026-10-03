theory Correctness
  imports "../formalization/ControlFlowSemantics"
begin

type_synonym precondition = "state \<Rightarrow> bool"
type_synonym postcondition = "state \<Rightarrow> state \<Rightarrow> llvm_value option \<Rightarrow> bool"
type_synonym block_preconditions = "((llvm_identifier * llvm_identifier) * (state \<Rightarrow> state \<Rightarrow> bool)) list"
type_synonym annotations = "(llvm_identifier * (precondition * block_preconditions * postcondition)) list"

context
  fixes program :: "llvm_program"
  fixes annotations :: "annotations"
begin

definition "wp_fs s Q \<equiv> \<forall>s'. (step_f program)\<^sup>*\<^sup>* s s' \<and> terminal_f s' \<longrightarrow> (\<not>error_state s' \<and> Q s')"

definition "function_hoare pre b f post \<equiv> \<forall>s. pre s \<longrightarrow> wp_fs (branchf s None b f) (\<lambda>s'. post s (state s') (ret_value s'))"

definition "function_correct f \<equiv>
  \<forall>body pre bpres post block.
    map_of program f = Some body
  \<and> map_of annotations f = Some (pre, bpres, post)
  \<and> first_label body = Some block
  \<longrightarrow> function_hoare pre block f post"

definition "correctness_notion \<equiv>
  \<forall>f. map_of program f \<noteq> None
  \<longrightarrow> function_correct f \<and> map_of annotations f \<noteq> None"

end

end