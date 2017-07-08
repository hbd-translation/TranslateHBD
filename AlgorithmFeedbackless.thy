section{*Feedbackless Algorithm*}

theory AlgorithmFeedbackless imports FeedbacklessPerm Hoare 
begin
context BaseOperationFeedbacklessVars
begin
definition "WhileFeedbackless = 
    while_stm (\<lambda> As . internal As \<noteq> {})
        [:As \<leadsto> As' . \<exists> A . A \<in> set As \<and> (out A) \<in> internal As \<and>  As'= map (CompA A) (As \<ominus> [A]):]"
    
definition "TranslateHBDFeedbackless = WhileFeedbackless o [-(\<lambda> As . Parallel_list As)-]"

definition "ok_fbless As = (Deterministic As \<and> loop_free As \<and> Type_OK As)"
    
definition "TranslateHBDRec = {. ok_fbless .} 
    o [:As \<leadsto> As' . \<exists> L . perm (VarFB (Parallel_list As)) L \<and> As' = fb_less L As :]"
  
    
lemma [simp]:"{.As. length (VarFB (Parallel_list As)) = w.} (TranslateHBDRec x) y \<Longrightarrow> [. - (\<lambda>As. internal As \<noteq> {}) .] x y"
  apply (simp add: TranslateHBDRec_def demonic_def assert_def le_fun_def assume_def, safe)
  apply (drule_tac x = y in spec, safe, simp)
  apply (drule_tac x = "[]" in spec, simp_all)
  by (simp add: internal_VarFB ok_fbless_def)
  
lemma internal_fb_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A \<in> internal As \<Longrightarrow>  internal (fb_less_step A (As \<ominus> [A])) = internal As - {out A}"
  by (metis fb_out_less_step_def internal_fb_out_less_step mem_get_comp_out mem_get_other_out)
  
  
lemma ok_fbless_fb_less_step: "ok_fbless As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A \<in> internal As \<Longrightarrow> ok_fbless (fb_less_step A (As \<ominus> [A]))"
  apply (simp add: ok_fbless_def, safe)
    apply (metis Deterministic_fb_out_less_step fb_out_less_step_def mem_get_comp_out mem_get_other_out)
   apply (metis fb_out_less_step_def loop_free_fb_out_less_step mem_get_comp_out mem_get_other_out)
    using Type_OK_fb_out_less_step_aux by blast
    
lemma map_CompA_fb_out_less_step: "Deterministic As \<Longrightarrow>
            loop_free As \<Longrightarrow>
            Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A \<in> internal As \<Longrightarrow> map (CompA A) (As \<ominus> [A]) = fb_out_less_step (out A) As"
  using fb_less_step_def fb_out_less_step_def mem_get_comp_out mem_get_other_out by presburger
    
lemma length_diff: "a \<in> set x \<Longrightarrow> length (x \<ominus> [a]) < length x"
  apply (induction x, simp_all, auto)
  using AAA_c by fastforce
    
thm perm_cons
 

lemma perm_cons_a: "\<And> y . a \<in> set x \<Longrightarrow> distinct x \<Longrightarrow> perm (x \<ominus> [a]) y \<Longrightarrow> perm x (a # y)"
  apply (subst perm_sym)
   apply (rule perm_cons, simp_all)
  by (subst perm_sym, simp_all)
    
    
lemma [simp]: "{.As. length (VarFB (Parallel_list As)) = w.} (TranslateHBDRec x) y \<Longrightarrow>
             [. \<lambda>As. internal As \<noteq> {} .]
              ([:As\<leadsto>As'.\<exists>A. A \<in> set As \<and> out A \<in> internal As \<and> As' = map (CompA A) (As \<ominus> [A]):] 
                ({.As. length (VarFB (Parallel_list As)) < w.} (TranslateHBDRec x))) y"
  apply (simp add: assert_def demonic_def TranslateHBDRec_def le_fun_def assume_def ok_fbless_def, safe)
      apply (simp add: map_CompA_fb_out_less_step)
      apply (simp add: VarFB_fb_out_less_step_gen internal_VarFB)
    apply (rule length_diff, simp)
  using Deterministic_fb_out_less_step map_CompA_fb_out_less_step apply presburger
  using loop_free_fb_out_less_step map_CompA_fb_out_less_step apply presburger
  using Type_OK_fb_out_less_step_new map_CompA_fb_out_less_step apply blast
  apply (simp add: map_CompA_fb_out_less_step)
  apply (drule_tac x = "(fb_less L (fb_out_less_step (out A) y))" in spec, safe, simp)
  apply (drule_tac x = "out A #  L" in spec, simp)
  apply (simp add: VarFB_fb_out_less_step_gen internal_VarFB)
  apply (subgoal_tac "distinct (VarFB (Parallel_list y))")
    apply (simp add: perm_cons_a)
    apply (simp add: VarFB_def Var_def)
    using distinct_inter io_diagram_distinct(2) io_diagram_parallel_list by blast
    
lemma Feedbackless_Rec_While_refinement: "TranslateHBDRec \<le> WhileFeedbackless"
  apply (simp add: WhileFeedbackless_def)
  apply (simp add: while_stm_def)
  apply (rule_tac p = "\<lambda> n . {. As . length (VarFB (Parallel_list As)) = n .} o TranslateHBDRec" in lfp_wf_induction_b)
    apply simp_all
  apply safe
    by (simp add: if_stm_def)

      
lemma [simp]:  "TranslateHBDRec o [-(\<lambda> As . Parallel_list As)-] \<le> TranslateHBDFeedbackless"
  apply (simp add: TranslateHBDFeedbackless_def)
  using Feedbackless_Rec_While_refinement by (simp add: le_fun_def)
    
thm FB_fb_less(1)

  
lemma Out_Parallel_fb_less: "\<And> As . Type_OK As \<Longrightarrow> loop_free As \<Longrightarrow> distinct L \<Longrightarrow> set L \<subseteq> internal As \<Longrightarrow> 
      Out (Parallel_list (fb_less L As)) = concat (map Out As) \<ominus> L"
  proof (induction L)
    case Nil
    then show ?case by (simp add: Out_Parallel)
  next
    case (Cons a L)
      
    have "a \<in> internal As"
      using Cons(5) by simp
      
    
    have [simp]: "Type_OK (fb_out_less_step a As)"
      using Cons(2)
      using Type_OK_fb_out_less_step_new \<open>a \<in> internal As\<close> by blast

    have A: "Out (Parallel_list (fb_less L (fb_out_less_step a As))) = concat (map Out (fb_out_less_step a As)) \<ominus> L"
      apply (rule Cons(1))
         apply simp
        apply (simp add: Cons.prems(2) \<open>a \<in> internal As\<close> local.Cons(2) loop_free_fb_out_less_step_internal)
      using Cons(4) apply simp
      by (metis Cons.prems(2) Cons.prems(3) Cons.prems(4) Diff_empty \<open>a \<in> internal As\<close> distinct.simps(2) 
          internal_fb_out_less_step local.Cons(2) order_trans set_subset_Cons subset_Diff_insert)
        
  define A where "A = get_comp_out a As"
  have [simp]: "A \<in> set As"
    using A_def Cons(5) by auto[1]
      
  from this have length_Out_A: "length (Out A) = 1"
    using \<open>Type_OK As\<close> by (unfold Type_OK_def, simp) 
  from this have "Out A = [out A]"
    by (simp add: Out_out)
      
  have "a \<in> set (Out A)"
    by (simp add: \<open>A \<equiv> get_comp_out a As\<close>)
      
  have Out_a: "out A = a"
    using \<open>Out A = [out A]\<close> \<open>a \<in> set (Out A)\<close> by auto
      
  have [simp]: "get_other_out a As = As \<ominus> [A]"
    using Out_a \<open>A \<in> set As\<close> local.Cons(2) mem_get_other_out by blast
 
  have B: "concat (map Out (As \<ominus> [A])) = concat (map Out As) \<ominus> [a]"
    by (metis \<open>get_other_out a As = As \<ominus> [A]\<close> concat_map_Out_get_other_out local.Cons(2))
        
    show ?case
      apply (simp add: A)
      apply (simp add: fb_out_less_step_def fb_less_step_def A_def [THEN sym])
      using length_Out_A  apply (simp add: BBB_b B)
      by (metis diff_cons)
  qed
    
lemma io_diagram_distinct_VarFB: "io_diagram A \<Longrightarrow> distinct (VarFB A)"
  apply (simp add: VarFB_def)
  by (simp add: io_diagram_distinct(2))
    
theorem fbless_correctness: "ok_fbless As \<Longrightarrow> perm (VarFB (Parallel_list As)) L \<Longrightarrow>
    in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As))"
proof (simp add:  ok_fbless_def, safe)
  assume [simp]: "Deterministic As"
  assume [simp]: "loop_free As"
  assume [simp]: "Type_OK As"
  assume P[simp]: "VarFB (Parallel_list As) <~~> L"
    
  define X where "X = Parallel_list As"
  define Y where "Y = Parallel_list (fb_less L As)"
    
  have [simp]: "In (FB (Parallel_list As)) = InFB X"
    apply (simp add: X_def [THEN sym] Y_def [THEN sym])
    by (simp add: FB_def Let_def InFB_def [THEN sym] VarFB_def [THEN sym])
    
  have [simp]: "In (FB (Parallel_list As)) <~~> In (Parallel_list (fb_less L As))"
    apply (simp add:  Y_def [THEN sym])
    by (rule_tac As = As and L = L in FB_fb_less(2), simp_all add: X_def Y_def)
      
  have length_VarFB_X: "length (VarFB X) =  length L"
    by (simp add: ListProp.perm_length X_def)
      
  have fb_perm_eq: "fb_perm_eq X"
    apply (simp add: X_def)
    by (rule fb_perm_eq_Parallel_list, simp_all)
    
  have [simp]: " Trs (FB (Parallel_list As)) 
      = [In (FB (Parallel_list As)) \<leadsto> In (Parallel_list (fb_less L As))] oo Trs (Parallel_list (fb_less L As))"
    apply (simp add: Y_def [THEN sym])
    apply (subst FB_fb_less(1) [THEN sym, of As _ L])
          apply simp_all
      apply (simp add: X_def)
      apply (simp add: X_def)
     apply (simp add: Y_def)
    apply (simp add: FB_def Let_def VarFB_def [THEN sym] X_def [THEN sym] InFB_def [THEN sym])
    using fb_perm_eq apply (simp add: fb_perm_eq_def)
    apply (drule_tac x = L in spec, safe)
     apply (simp_all add: length_VarFB_X OutFB_def)
    using ListProp.perm_sym X_def \<open>VarFB (Parallel_list As) <~~> L\<close> by blast
      
  have A: "distinct (VarFB (Parallel_list As))"
    by (simp add: io_diagram_parallel_list)

    have [simp]: "Out (FB (Parallel_list As)) = Out (Parallel_list (fb_less L As))"
      apply (simp add: FB_def Let_def X_def [THEN sym])
      apply (subst Out_Parallel_fb_less, simp_all)
      using A P
      using dist_perm apply blast
       apply (simp add: internal_VarFB)
        by (metis Out_Parallel P VarFB_def X_def perm_diff_eq)
        
      
  show "in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As))"
    apply (simp add: in_equiv_def)
    using \<open>In (FB (Parallel_list As)) <~~> In (Parallel_list (fb_less L As))\<close> by simp
qed

lemma Hoare_TranslateHBDRec: "Hoare (\<lambda> As . As = As_init \<and> ok_fbless As) 
    (TranslateHBDRec o [-(\<lambda> As . Parallel_list As)-]) 
    (\<lambda> A . in_equiv (FB (Parallel_list As_init)) A)"
  apply (simp add: Hoare_def le_fun_def TranslateHBDRec_def update_def demonic_def assert_def ok_fbless_def, safe)
  by (rule fbless_correctness, simp_all add: ok_fbless_def)
        
theorem TranslateHBDFeedbacklessCorrectness: "Hoare (\<lambda> As . As = As_init \<and> ok_fbless As) 
    TranslateHBDFeedbackless
    (\<lambda> A . in_equiv (FB (Parallel_list As_init)) A)"
  apply (rule_tac S = "(TranslateHBDRec o [-(\<lambda> As . Parallel_list As)-]) " in  refinement_hoare)
   apply simp_all
  by (simp add: Hoare_TranslateHBDRec)

 end
  
end