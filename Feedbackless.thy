theory Feedbackless imports DiagramFeedbackless
begin
  context BaseOperationFeedbacklessVars
begin

    
lemma [simp]: "Type_OK As \<Longrightarrow> a \<in> internal As \<Longrightarrow> out (get_comp_out a As) = a"
  apply (subgoal_tac "a \<in> set (Out (get_comp_out a As))")
   apply (subst (asm) Out_out)
    apply (simp add: Type_OK_def)
  by simp_all


    
lemma internal_Type_OK_simp: "Type_OK As \<Longrightarrow> internal As = {a . (\<exists> A \<in> set As . out A = a \<and> (\<exists> B \<in> set As. a \<in> set (In B)))}"
  apply (subgoal_tac "\<And> A . A \<in> set As \<Longrightarrow> Out A = [out A]")
   apply (simp add: internal_def)
   apply auto
  using Type_OK_out by blast  

lemma  Type_OK_fb_less: "\<And> As . Type_OK As \<Longrightarrow> loop_free As \<Longrightarrow> distinct x \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> Type_OK (fb_less x As)"
  proof (induction x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
      
    have [simp]: "Type_OK As"
      by (simp add: Cons)
     
    have [simp]: "a \<in> internal As"
      using Cons(5) by simp
    from this obtain A where [simp]: "A \<in> set As" and [simp]: "out A = a"
      by (subst (asm) internal_Type_OK_simp,simp_all, blast)

    show ?case
      apply simp
      apply (rule Cons(1))
         apply (rule_tac As = As in Type_OK_fb_out_less_step_new, simp_all)
        apply (rule_tac A = A in loop_free_fb_out_less_step)
           apply (simp_all add: Cons)
      using \<open>distinct (a#x)\<close> apply simp
      apply (subst internal_fb_out_less_step, simp_all add: Cons)
      using Cons.prems(3) Cons.prems(4) by auto
  qed

  
    
lemma fb_Parallel_list_fb_out_less_step: 
  assumes [simp]: "Type_OK As"
    and "Deterministic As"
    and "loop_free As"
    and internal: "a \<in> internal As"
    and X: "X = Parallel_list As"
    and Y: "Y = (Parallel_list (fb_out_less_step a As))"
    and [simp]: "perm y (In Y)"
    and [simp]: "perm z (Out Y)"
  shows "fb ([a # y \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # z]) = [y \<leadsto> In Y] oo Trs Y oo [Out Y \<leadsto> z]" and "perm (a # In Y) (In X)"
proof -
  have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> io_diagram A"
    using Type_OK_def assms(1) by blast

  define A where "A = get_comp_out a As"
  from internal have [simp]: "A \<in> set As" and [simp]: "out A = a"
    by (simp_all add: A_def)
      
  have [simp]: "get_other_out a As = As \<ominus>[A]"
    using \<open>A \<in> set As\<close> \<open>out A = a\<close> assms(1) mem_get_other_out by blast
      
  have [simp]: "length (Out A) = 1"
    using \<open>Type_OK As\<close> Type_OK_def \<open>A \<in> set As\<close> by blast
  
  have [simp]: "a \<notin> set (In A)"
    using Type_OK_loop_free_elem \<open>A \<in> set As\<close> \<open>out A = a\<close> assms(1) assms(3) by blast

  have "io_diagram Y"
    using Type_OK_fb_out_less_step_new Y assms(1) assms(3) internal io_diagram_parallel_list by blast
        
  from this have dist_a_Y: "distinct (a # In Y)"
    apply simp
    by (simp add: Y In_Parallel fb_out_less_step_def A_def [THEN sym] fb_less_step_def In_CompA set_addvars set_diff Out_out)
      
  have "io_diagram X"
    by (simp add: X io_diagram_parallel_list)
      
  from this have [simp]: "distinct (In X)"
    by (simp)
            
  from internal obtain B where [simp]: "B \<in> set As" and [simp]: "a \<in> set (In B)"
    by (simp add: internal_def, auto)
      
  have [simp]: "B \<noteq> A"
    using \<open>a \<in> set (In B)\<close> \<open>a \<notin> set (In A)\<close> by blast
      
      
  show "perm (a # In Y) (In X)"
    apply (rule set_perm)
    using dist_a_Y apply simp
      apply simp
    apply (simp add: X Y)
    apply (simp add: In_Parallel )
    apply (simp add: fb_out_less_step_def A_def [THEN sym])
    apply (simp add: fb_less_step_def In_CompA, safe)
      apply (auto simp add: set_diff set_addvars)
    using internal apply (subst (asm) internal_Type_OK_simp, simp_all)
     apply (case_tac "a \<in> set (In xa)")
      apply (auto simp add: set_diff set_addvars)
      apply (case_tac "xa = A")
    apply (drule_tac x = B in bspec, simp_all add: set_diff set_addvars)
    apply (drule_tac x = xa in bspec, simp_all add: set_diff set_addvars)
    by (case_tac "a \<in> set (In xa)", simp_all add: set_diff set_addvars Out_out)
    

  from this have [simp]: "perm (a # y) (In X)"
    apply (rule_tac y = "a # In Y" in perm_trans)
     by simp_all
      
  from this have dist_a_y: "distinct (a # y)"
    using io_diagram_distinct(1) X assms(1) dist_perm perm_sym io_diagram_parallel_list by blast
      
    
  define Z where "Z =  CompA A (Parallel_list (As \<ominus> [A]))"
      
  thm fb_less_step_compA
    
  have equiv_Y_Z: "in_equiv Y Z"
    apply (simp add: Y Z_def fb_out_less_step_def A_def[THEN sym])
    apply (rule fb_less_step_compA, simp_all)
    using Deterministic_def \<open>A \<in> set As\<close> assms(2) by blast

  from this have [simp]: "perm (In Y) (In Z)" and Y_Z: "Trs Y = [In Y \<leadsto> In Z] oo Trs Z" and [simp]: "Out Z = Out Y"
    by (simp_all add: in_equiv_def)
      
  have [simp]: "perm y (In Z)"
    by (rule_tac y = "In Y" in perm_trans, simp_all)
      
  have [simp]: "io_diagram Z"
    by (metis Type_OK_def io_diagram_CompA Type_OK_diff Z_def \<open>A \<in> set As\<close> assms(1) io_diagram_parallel_list)

  have "fb ([a # y \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # z]) 
        = fb ([a # y \<leadsto> In (Parallel_list As)] oo ([In X \<leadsto> concat (map In As)] oo parallel_list (map Trs As)) oo [Out X \<leadsto> a # z])"
    by (simp add: X Trs_Parallel_list)
  also have "... = fb (([a # y \<leadsto> In X] oo [In X \<leadsto> concat (map In As)]) oo parallel_list (map Trs As) oo [Out X \<leadsto> a # z])"
    by (simp_all add: X comp_assoc TI_parallel_list TO_parallel_list Out_Parallel)
  also have "... = fb ([a # y \<leadsto> concat (map In As)] oo parallel_list (map Trs As) oo [Out X \<leadsto> a # z])"
    apply (subgoal_tac "[a # y \<leadsto> In X] oo [In X \<leadsto> concat (map In As)] = [a # y \<leadsto> concat (map In As)]")
     apply simp
    apply (subst switch_comp)
    using dist_a_y apply blast
      apply simp
    by (simp add: X In_Parallel, auto)
  also have "... =  [y \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> z]"
    thm fb_CompA
    apply (subst fb_CompA [of As A a Z _ _ _ B], simp_all add: X)
    by (simp add: Z_def)
  
  also have "... = [y \<leadsto> In Y] oo Trs Y oo [Out Y \<leadsto> z]"
    apply simp
    apply (rule_tac f = "\<lambda> X . X oo [Out Y \<leadsto> z]" in arg_cong)
    apply (simp add: Y_Z)
    apply (simp add: comp_assoc[THEN sym])
    apply (subst switch_comp, simp_all)
    using dist_a_y by auto
      
  finally show "fb ([a # y \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # z]) = [y \<leadsto> In Y] oo Trs Y oo [Out Y \<leadsto> z]"
    by simp
qed


lemma internal_In_Parallel_list: "a \<in> internal As \<Longrightarrow> a \<in> set (In (Parallel_list As))"
  by (simp add: In_Parallel internal_def)

lemma internal_Out_Parallel_list: "a \<in> internal As \<Longrightarrow> a \<in> set (Out (Parallel_list As))"
  by (simp add: Out_Parallel internal_def)
  
    
theorem fb_power_internal_fb_less: "\<And> As X Y . Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> set L \<subseteq> internal As 
  \<Longrightarrow> distinct L \<Longrightarrow>
   X = (Parallel_list As) \<Longrightarrow> Y = Parallel_list (fb_less L As) \<Longrightarrow>
   (fb ^^ length (L)) ([L @ (In X \<ominus> L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ (Out X \<ominus> L)]) = [In X \<ominus> L \<leadsto> In Y] oo Trs Y
  \<and> perm (In X \<ominus> L) (In Y)"
  proof (induction L)
    case Nil
    have [simp]: "io_diagram X"
      apply (simp add: Nil)
      by (simp add: Nil.prems(3) io_diagram_parallel_list)
    have [simp]: "Y = X"
      by (simp add: Nil)
    then show ?case
      by (simp_all add: InFB_def)
  next
    case (Cons a L)
    have type_As[simp]: "Type_OK As"
      by (simp add: Cons)
    have [simp]: "io_diagram X"
      apply (simp add: Cons)
      by (simp add: io_diagram_parallel_list)

    from type_As have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> io_diagram A"
      by (unfold Type_OK_def, simp)
        
   have internal_a[simp]: "a \<in> internal As"
     using Cons.prems(4) by auto

   have internal_a[simp]: "set L \<subseteq> internal As"
     using Cons.prems(4) by auto
        

   have "a \<in> set (In X)"
     apply (simp add: Cons)
     apply (rule internal_In_Parallel_list)
     by (simp add: Cons)
       
        
    have "set L \<subseteq> set (In X)"
     apply (simp add: Cons, safe)
      apply (rule internal_In_Parallel_list)
      using internal_a by blast
        
    have "distinct (In X)"
      by simp

    have perm_a[simp]: "perm (a # L @ (In X \<ominus> (a # L))) (In X)"
      apply (subgoal_tac "perm ((a # L) @ (In X \<ominus> (a # L))) (In X)")
       apply simp
      by (metis Cons.prems(5) \<open>a \<in> set (In X)\<close> \<open>distinct (In X)\<close> \<open>set L \<subseteq> set (In X)\<close> append_Nil diff.simps(2) diff_subset perm_switch)
        
    from this have Ba: "distinct (a # L @ (In X \<ominus> (a # L)))"
      using io_diagram_distinct(1) BaseOperationFeedbacklessVars_axioms \<open>io_diagram X\<close> dist_perm perm_sym by blast

    from perm_a and this have [simp]: "perm (L @ (In X \<ominus> (a # L))) (In X \<ominus> [a])"
    proof -
      have f1: "distinct (In X \<ominus> [a])"
        by (meson Ba dist_perm distinct_diff perm_a)
      have "{a} = set [a]"
        by (metis list.set(1) list.set(2))
      then show ?thesis
        using f1 by (metis (no_types) Ba Diff_insert_absorb distinct.simps(2) list.set(2) perm_a perm_set_eq set_diff set_perm)
    qed
      
   thm fb_Parallel_list_fb_out_less_step
     
   define Z where "Z = Parallel_list (fb_out_less_step a As)"
            
   have [simp]: "io_diagram Y"
     apply (unfold Cons)
     apply (rule io_diagram_parallel_list)
       apply (rule Type_OK_fb_less, simp_all)
     using Cons.prems(2) apply auto[1]
     using Ba by auto[1]
       
       
   have [simp]: "distinct (In X \<ominus> (a # L))"
     by (simp)

   have "io_diagram Z"
     apply (simp add: Z_def)
     apply (subst io_diagram_parallel_list, simp_all)
     by (metis Cons.prems(4) Type_OK_fb_out_less_step_new \<open>Type_OK As\<close> insert_subset list.simps(15))
       
       
   from this have dist_InZ[simp]: "distinct (In Z)"
     by simp
       

   have dist_L_InFB_X: "distinct (L @ (In X \<ominus> (a # L)))"
     apply (simp add: Cons, safe)
     using Ba apply auto[1]
     using Cons.prems(6) \<open>distinct (In X \<ominus> a # L)\<close> apply blast
     by (simp add: InFB_def set_diff)
       
   have [simp]: "perm (a # In Z) (In X)"
     apply (rule_tac fb_Parallel_list_fb_out_less_step [of As _ _ _ "In Z" "Out Z"])
     by (simp_all add: Cons Z_def)
       
   have "distinct (In X)"
     using Ba dist_perm perm_a by blast
       
   have [simp]: " perm (L @ (In X \<ominus> (a # L))) (In Z)"
     apply (rule_tac y = " (In X \<ominus> [a])" in perm_trans)
      apply (simp add: InFB_def)
       apply (subst perm_sym, simp_all)
     using \<open>distinct (In X)\<close>
     by (rule distinct_perm_cons, simp)
       
   thm concat_map_Out_get_other_out
   thm map_Out_fb_out_less_step
   thm map_Out_fb_less_step
     
   have "distinct (Out X)"
     using \<open>io_diagram X\<close> io_diagram_def by blast
       
   have "set (a # L) \<subseteq> set (Out X)"
     apply (unfold Cons)
     apply (safe)
     apply (rule internal_Out_Parallel_list)
     using Cons.prems(4) by blast
     
   have "perm (a # L @ (Out X \<ominus> (a # L))) (Out X)"
     by (metis Cons.prems(5) \<open>distinct (Out X)\<close> \<open>set (a # L) \<subseteq> set (Out X)\<close> append_Cons append_Nil diff_subset perm_switch)
       
   from this have "perm (L @ (Out X \<ominus> (a # L))) (Out X \<ominus> [a])"
     by (simp add: distinct_perm_cons)
       
   have [simp]: "distinct (Out Z)"
     by (simp add: \<open>io_diagram Z\<close>)
       
  define A where "A = get_comp_out a As"
     
  from internal_a have [simp]: "A \<in> set As" and [simp]: "out A = a"
    by (simp_all add: A_def)
      
  have get_other_out[simp]: "get_other_out a As = As \<ominus>[A]"
    using \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_other_out by blast
 
  have [simp]: "perm (L @ (Out X \<ominus> (a # L))) (Out Z)"
     apply (rule_tac y = "Out X \<ominus> [a]" in perm_trans)
     using \<open>perm (L @ (Out X \<ominus> (a # L))) (Out X \<ominus> [a])\<close> apply blast
     apply (rule set_perm)
       apply simp_all
     apply (simp add: Cons Z_def Out_Parallel del:set_map)
     apply (subst map_Out_fb_out_less_step[of A], simp_all add: set_diff)
     apply safe
       apply simp_all
       apply (case_tac "a = x", simp)
       apply (drule_tac x = aa in bspec, simp_all)
       using Cons(4)
         apply (metis Type_OK_out \<open>out A = a\<close> empty_iff list.set(1) set_ConsD)
        apply blast
         using Cons(4)
         by (simp add: A_def Type_OK_out mem_get_comp_out)

       have set_Out_Z: "set (Out Z) = set L \<union> set (Out X \<ominus> (a # L))"
         
         by (metis ListProp.perm_set_eq \<open>L @ (Out X \<ominus> a # L) <~~> Out Z\<close> set_append)
      
       have set_In_Z: "set (In Z) = set L \<union> set (In X \<ominus> (a # L))"
         by (metis ListProp.perm_set_eq \<open>L @ (In X \<ominus> a # L) <~~> In Z\<close> set_append)
      
  have [simp]: "distinct L"
    using dist_L_InFB_X by auto

  have [simp]: "set L \<subseteq> internal (fb_out_less_step a As)"
    by (metis Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)

  have [simp]: "perm (In X \<ominus> (a # L)) (In Z \<ominus> L)"
    apply (subgoal_tac "perm (L @ (In X \<ominus> (a # L))) (L @ (In Z \<ominus> L))")
     apply (metis add_left_cancel perm_mset union_code)
    apply (rule_tac y = "In Z" in perm_trans)
     apply simp
    by (metis \<open>distinct L\<close> append_Nil diff_subset dist_InZ perm_switch perm_sym set_In_Z sup_ge1)
      

  from internal_a have [simp]: "Deterministic (fb_out_less_step a As)"
    using Cons.prems(1) Deterministic_fb_out_less_step \<open>A \<in> set As\<close> \<open>out A = a\<close> type_As by blast
    
  from internal_a have [simp]: "loop_free (fb_out_less_step a As)"
    using Cons.prems(2) \<open>A \<in> set As\<close> \<open>out A = a\<close> loop_free_fb_out_less_step type_As by blast

  from internal_a have [simp]: "Type_OK (fb_out_less_step a As)"
    by (simp add: A_def Type_OK_fb_out_less_step_aux fb_out_less_step_def)
      
      
   have [simp]: "perm (In X \<ominus> (a # L)) (In Y)"
    apply (rule_tac y = "In Z \<ominus> L" in perm_trans, simp_all)
     apply (subst Cons(1) [of "fb_out_less_step a As" "Z" "Y"], simp_all)
      apply (simp add: Z_def)
     by (simp add: Cons)
       
   have [simp]: "set (In Y) \<subseteq> set (In Z \<ominus> L)"
     by (metis \<open>perm (In X \<ominus> (a # L)) (In Y)\<close> \<open>perm (In X \<ominus> (a # L)) (In Z \<ominus> L)\<close> order_refl perm_set_eq)

   have A: "(fb  ([a # L @ (In X \<ominus> (a # L)) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # L @ (Out X \<ominus> (a # L))])) = [L @ (In X \<ominus> (a # L)) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> (a # L))]"
     apply (subst fb_Parallel_list_fb_out_less_step [of As], simp_all add: Cons)
       apply (simp add: Z_def)
     by (simp_all add: Cons(7) [THEN sym])
     
   have OutFB_X_Z: "Out X \<ominus> (a # L) = Out Z \<ominus> L"
     apply (subst perm_diff_eq[of _ "a # L"])
      apply (simp add: Cons(5))
     apply (subst (2)  perm_diff_eq[of _ "L"])
      apply simp
     apply (simp add: Cons Z_def Out_Parallel)
     apply (subst map_Out_fb_out_less_step [of A], simp_all add: concat_map_Out_get_other_out del: get_other_out)
     by (meson diff_cons)
       
   have "(fb ^^ length (a # L)) ([(a # L) @ (In X \<ominus> a # L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> (a # L) @ (Out X \<ominus> a # L)]) 
      = (fb ^^ (length L)) (fb  ([a # L @ (In X \<ominus> a # L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # L @ (Out X \<ominus> (a # L))]))"
     by (simp add: funpow_swap1)
   also have "... = (fb ^^ length L) ([L @ (In X \<ominus> a # L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> (a # L))])"
     by (simp add: A)
   also have "... = (fb ^^ length L) (([L @ (In X \<ominus> a # L) \<leadsto> L @ (In Z \<ominus> L)] oo [L @ (In Z \<ominus> L) \<leadsto> In Z]) oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> (a # L))])"
     apply (subgoal_tac "[L @ (In X \<ominus> a # L) \<leadsto> L @ (In Z \<ominus> L)] oo [L @ (In Z \<ominus> L) \<leadsto> In Z] = [L @ (In X \<ominus> a # L) \<leadsto> In Z]")
      apply simp
     by (subst switch_comp, simp_all add: set_diff, auto)

   also have "... = (fb ^^ length L) ([L @ (In X \<ominus> a # L) \<leadsto> L @ (In Z \<ominus> L)] oo ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> a # L)]))"
     using \<open>io_diagram Z\<close> by (simp add: comp_assoc)
   
   also have "... = (fb ^^ length L) ([L \<leadsto> L] \<parallel> [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> a # L)]))"
     using dist_L_InFB_X par_switch by auto
     
       also have "... = [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo (fb ^^ length (TVs L)) ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> a # L)])"
     apply (subst fb_indep_left [THEN sym])
     using \<open>io_diagram Z\<close> apply (simp add: fbtype_def )
     apply (subgoal_tac "[L \<leadsto> L] = ID (TVs L)")
       apply (simp)
     using \<open>distinct L\<close> distinct_id by blast
  
   also have "... = [(In X \<ominus> a # L) \<leadsto> (In Z \<ominus> L)] oo (fb ^^ length L) ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out Z \<ominus> L)])"
     by (simp add: OutFB_X_Z)
       
   also have "... = [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo ([In Z \<ominus> L \<leadsto> In Y] oo Trs Y)"
     apply (subst Cons(1) [of "fb_out_less_step a As" "Z" "Y"])
           apply (simp_all add: Cons)
     by (simp add: Z_def)
   also have "... = [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo [In Z \<ominus> L \<leadsto> In Y] oo Trs Y"
     by (simp add:  comp_assoc)
   also have "... = [(In X \<ominus> a # L) \<leadsto> In Y] oo Trs Y"
     by (subst switch_comp, simp_all)

    finally show ?case by simp
  qed
    
  thm fb_power_internal_fb_less

    
theorem FB_fb_less:
  assumes [simp]: "Deterministic As"
    and [simp]: "loop_free As" 
    and [simp]: "Type_OK As"
    and [simp]: "perm (VarFB X) L"
    and X: "X = (Parallel_list As)"
    and Y: "Y = Parallel_list (fb_less L As)"
  shows "(fb ^^ length (L)) ([L @ InFB X \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ OutFB X]) = [InFB X \<leadsto> In Y] oo Trs Y"
    and B: "perm (InFB X) (In Y)"
proof -
  have [simp]: "set L \<subseteq> internal As"
    using assms(4) X internal_VarFB by auto
      
  have "distinct (Out (Parallel_list As))"
    by (metis Out_Parallel Type_OK_def assms(3))
      
  from this have "distinct (VarFB X)"
    by (simp add: VarFB_def X)
      
  from this have [simp]: "distinct L"
    using assms(4) dist_perm by blast

  have [simp]: "(fb ^^ length L) ([L @ (In X \<ominus> L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ (Out X \<ominus> L)]) = [In X \<ominus> L \<leadsto> In Y] oo Trs Y"
    and [simp]: "perm (In X \<ominus> L) (In Y)"
     apply (subst fb_power_internal_fb_less, simp_all add: X Y)
    by (subst fb_power_internal_fb_less, simp_all)
      
  have [simp]: "InFB X = In X \<ominus> L"
    by (simp add: InFB_def perm_diff_eq)
      
  have [simp]: "OutFB X = Out X \<ominus> L"
    by (simp add: OutFB_def perm_diff_eq)
      
  show "(fb ^^ length (L)) ([L @ InFB X \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ OutFB X]) = [InFB X \<leadsto> In Y] oo Trs Y"
    by simp
  show "perm (InFB X) (In Y)"
    by simp
qed

    
definition "fb_perm_eq A = (\<forall> x. perm x (VarFB A) \<longrightarrow> 
  (fb ^^ length (VarFB A)) ([VarFB A @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> VarFB A @ OutFB A]) = 
  (fb ^^ length (VarFB A)) ([x @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> x @ OutFB A]))"
  
lemma fb_perm_eq_simp: "fb_perm_eq A = (\<forall> x. perm x (VarFB A) \<longrightarrow> 
  Trs (FB A) = (fb ^^ length (VarFB A)) ([x @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> x @ OutFB A]))"
  by (simp add: fb_perm_eq_def FB_def Let_def VarFB_def InFB_def OutFB_def)
  
lemma in_equiv_in_out_equiv: "io_diagram B \<Longrightarrow> in_equiv A B \<Longrightarrow> in_out_equiv A B"
  by (simp add: in_equiv_def in_out_equiv_def)

  thm in_equiv_fb_fb_less_step
  thm fb_CompA
  thm fb_less_step_compA
  thm fb_out_less_step_def

      
    
lemma [simp]: "distinct (concat (map f As)) \<Longrightarrow> distinct (concat (map f (As \<ominus> [A])))"
  apply (induction As, auto)
  by (simp add: set_diff, auto)
    

lemma set_op_list_addvars: "set (op_list [] op \<oplus> x) = (\<Union> a \<in> set x . set a)"
  by (induction x, auto simp add: set_addvars)
    
          
end
  
end