theory Syntax
  imports "../Word_Lib/Word_Names" "HOL-Library.Mapping"
begin

section "LLVM AST"


subsection "Types and values"

datatype llvm_type = i1 | i32 | i64 | addr_type

type_synonym memory_model_address = nat
datatype llvm_address = saddr memory_model_address | haddr memory_model_address | gaddr memory_model_address

datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | addr llvm_address | poison

datatype llvm_identifier = is_lid: lid string | gid string



datatype llvm_value_ref = reg llvm_identifier | val llvm_value

(* Should only have a memory address or memory address... *)
type_synonym llvm_pointer = llvm_value_ref


subsection "Instructions"

type_synonym llvm_align = int

datatype llvm_add_wrap = add_nuw | add_nsw | add_nuw_nsw | add_default
datatype llvm_compare_condition = comp_eq | comp_ne
                                | comp_ugt | comp_uge | comp_ult | comp_ule
                                | comp_sgt | comp_sge | comp_slt | comp_sle
type_synonym llvm_same_sign = bool

datatype llvm_phi_node = phi llvm_identifier llvm_type "(llvm_identifier * llvm_value_ref) list"


datatype llvm_instruction = alloca llvm_identifier llvm_type "llvm_align option"
                          | store llvm_type llvm_value_ref llvm_pointer "llvm_align option"
                          | load llvm_identifier llvm_type llvm_pointer "llvm_align option"
                          | add llvm_identifier llvm_add_wrap llvm_type llvm_value_ref llvm_value_ref
                          | icmp llvm_identifier llvm_same_sign llvm_compare_condition llvm_type llvm_value_ref llvm_value_ref
                          | is_call: call "llvm_identifier option" llvm_type llvm_identifier "(llvm_type * llvm_value_ref) list"

datatype llvm_terminator_instruction = ret "(llvm_type * llvm_value_ref) option"
                                     | br_i1 llvm_value_ref llvm_identifier llvm_identifier
                                     | br_label llvm_identifier


subsection "Blocks, functions, programs"

type_synonym llvm_instruction_block = "(llvm_phi_node list * llvm_instruction list * llvm_terminator_instruction)"

type_synonym llvm_labeled_blocks = "(llvm_identifier * llvm_instruction_block) list"

datatype llvm_block_return = return_value "llvm_value option"
                           | branch_label llvm_identifier

datatype llvm_function = func llvm_type (params: "(llvm_identifier * llvm_type) list") (blocks: llvm_labeled_blocks)
hide_const (open) llvm_function.blocks

type_synonym llvm_program = "(llvm_identifier * llvm_function) list"




end