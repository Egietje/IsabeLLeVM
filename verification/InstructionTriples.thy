theory InstructionTriples
  imports WeakestPreconditions
begin

lemma wp_case_value_addr_intro[wp_rules]:
  assumes "\<And>x. a = addr x \<Longrightarrow> wp (f x) Q"
  assumes "\<not>(\<exists>x. a = addr x) \<Longrightarrow> wp g Q"
  shows "wp (case a of addr x \<Rightarrow> f x | _ \<Rightarrow> g) Q"
  using assms
  unfolding wp_def
  by (cases "a"; auto)



lemma alloca_triple[THEN consequence, rearranged (1,0), wp_rules]:
  assumes "is_lid name"
  shows "wp (execute_alloca name s) (\<lambda>s'. \<exists>a. (register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (addr (saddr a))) \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr a := Some mem_unset) \<and> memory_\<alpha> s (saddr a) = None))"
  using assms
  unfolding execute_alloca_def
  by (intro wp_rules; auto)


lemma store_triple[THEN consequence, rearranged (0,2,3,1), wp_rules]:
  assumes "register_\<alpha> s pointer = Some (addr a)" "valid_memory_address s a"
  assumes "register_\<alpha> s value = Some v"
  shows "wp (execute_store value pointer s) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v)) \<and> register_\<alpha> s' = register_\<alpha> s)"
  unfolding execute_store_def
  using assms
  apply simp
  apply (intro wp_rules) by auto


lemma load_triple[THEN consequence, rearranged (0,1,3,2), wp_rules]:
  assumes "register_\<alpha> s pointer = Some (addr a)" "memory_\<alpha> s a = Some (mem_val v)" "is_lid name"
  shows "wp (execute_load name pointer s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v))"
  unfolding execute_load_def
  using assms
  apply simp
  by (intro wp_rules; auto)


lemma add32_triple[THEN consequence, rearranged (0,1,4,2,3), wp_rules]:
  assumes "register_\<alpha> s v1 = Some (vi32 v1')" "register_\<alpha> s v2 = Some (vi32 v2')" "add_no_poison32 wrap v1' v2'" "is_lid name"
  shows "wp (execute_add name wrap v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi32 (v1' + v2'))))"
  using assms
  unfolding execute_add_def
  by (intro wp_rules; simp; auto; intro wp_rules; simp)

lemma add64_triple[THEN consequence, rearranged (0,1,4,2,3), wp_rules]:
  assumes "register_\<alpha> s v1 = Some (vi64 v1')" "register_\<alpha> s v2 = Some (vi64 v2')" "add_no_poison64 wrap v1' v2'" "is_lid name"
  shows "wp (execute_add name wrap v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi64 (v1' + v2'))))"
  using assms
  unfolding execute_add_def
  by (intro wp_rules; simp; auto; intro wp_rules; simp)


lemma icmp1_triple[THEN consequence, rearranged (0,1,4,2,3), wp_rules]:
  assumes "register_\<alpha> s v1 = Some (vi1 v1')" "register_\<alpha> s v2 = Some (vi1 v2')" "(if ss then same_signs1 v1' v2' else True)" "is_lid name"
  shows "wp (execute_icmp name ss cond v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_1 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_rules; auto; intro wp_rules; auto)

lemma icmp32_triple[THEN consequence, rearranged (0,1,4,2,3), wp_rules]:
  assumes "register_\<alpha> s v1 = Some (vi32 v1')" "register_\<alpha> s v2 = Some (vi32 v2')" "(if ss then same_signs32 v1' v2' else True)" "is_lid name"
  shows "wp (execute_icmp name ss cond v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_32 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_rules; auto; intro wp_rules; auto)

lemma icmp64_triple[THEN consequence, rearranged (0,1,4,2,3), wp_rules]:
  assumes "register_\<alpha> s v1 = Some (vi64 v1')" "register_\<alpha> s v2 = Some (vi64 v2')" "(if ss then same_signs64 v1' v2' else True)" "is_lid name"
  shows "wp (execute_icmp name ss cond v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_64 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_rules; auto; intro wp_rules; auto)


lemma phi_triple[THEN consequence, rearranged (0,2,3,4,6,1,5),  wp_rules]:
  assumes "p = phi name t values"
  assumes "distinct (map fst values)"
  assumes "pre = Some pre'" "map_of values pre' = Some v" "register_\<alpha> s v = Some v'" "is_lid name"
  shows "wp (execute_phi pre p s) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding execute_phi_def
  using assms
  by (simp; intro wp_rules; simp; intro wp_rules; simp)


lemma [wp_rules]: "wp (execute_alloca name s) Q \<Longrightarrow> wp (execute_instruction (alloca name type align) s) Q"
  by simp
lemma [wp_rules]: "wp (execute_store value pointer s) Q \<Longrightarrow> wp (execute_instruction (store type value pointer align) s) Q"
  by simp
lemma [wp_rules]: "wp (execute_load name pointer s) Q \<Longrightarrow> wp (execute_instruction (load name type pointer align) s) Q"
  by simp
lemma [wp_rules]: "wp (execute_add name wrap v1 v2 s) Q \<Longrightarrow> wp (execute_instruction (add name wrap type v1 v2) s) Q"
  by simp
lemma [wp_rules]: "wp (execute_icmp name same_sign cond v1 v2 s) Q \<Longrightarrow> wp (execute_instruction (icmp name same_sign cond type v1 v2) s) Q"
  by simp

end
