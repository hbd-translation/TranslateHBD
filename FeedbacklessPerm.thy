section{*The order of internal states does not change the result of feedbackless*}

theory FeedbacklessPerm imports Feedbackless
begin
  context BaseOperationFeedbacklessVars
begin
  
lemma [simp]: "out B \<notin> set (In A) \<Longrightarrow> CompA B A = A"
  by (simp add: CompA_def)

lemma [simp]: "out B \<in> set (In A) \<Longrightarrow> CompA B A = B ;; A"
  by (simp add: CompA_def)

lemma [simp]: "set (Out A) \<subseteq> set (In B) \<Longrightarrow> Out ((A ;; B)) = Out B"
  by (simp add: Comp_def out_def Let_def Var_def diff_eq subsetset_inter)
    
    
lemma [simp]: "set (Out A) \<subseteq> set (In B) \<Longrightarrow> out ((A ;; B)) = out B"
  by (simp add: Comp_def out_def Let_def Var_def diff_eq subsetset_inter)
    

lemma switch_par_comp3: 
  assumes [simp]: "distinct x" and
    [simp]: "distinct y"
    and [simp]: "distinct z" 
    and [simp]: "distinct u"
    and [simp]: "set y \<subseteq> set x"
    and [simp]: "set z \<subseteq> set x"
    and [simp]: "set u \<subseteq> set x"
    and [simp]: "set y' \<subseteq> set y"
    and [simp]: "set z' \<subseteq> set z" 
    and [simp]: "set u' \<subseteq> set u"
    shows "[x \<leadsto> y @ z @ u] oo [y \<leadsto> y'] \<parallel> [z \<leadsto> z'] \<parallel> [u \<leadsto> u'] = [x \<leadsto> y' @ z' @ u']"
      proof -
        have [simp]: "[x \<leadsto> y @ z @ u] = [x \<leadsto> y @ x] oo [y \<leadsto> y] \<parallel> [x \<leadsto> z @ u]"
          by (subst switch_par_comp_Subst, simp_all add:)
        show "[x \<leadsto> y @ z @ u] oo [y \<leadsto> y'] \<parallel> [z \<leadsto> z'] \<parallel> [u \<leadsto> u'] = [x \<leadsto> y' @ z' @ u']"
          apply simp
          apply (subst comp_assoc, simp_all add: par_assoc)
          apply (subst comp_parallel_distrib, simp_all)
          apply (simp add: switch_par_comp)
          apply (subst switch_par_comp, simp_all)
          using assms(10) assms(6) assms(7) assms(9) by blast
      qed
        
lemma switch_par_comp_Subst3: 
  assumes [simp]: "distinct x" and [simp]: "distinct y'" and [simp]: "distinct z'" and [simp]: "distinct t'"
    and [simp]: "set y \<subseteq> set x" and [simp]: "set z \<subseteq> set x" and [simp]: "set t \<subseteq> set x"
    and [simp]: "set u \<subseteq> set y'" and [simp]: "set v \<subseteq> set z'" and [simp]: "set w \<subseteq> set t'"
    and [simp]: "TVs y = TVs y'" and [simp]: "TVs z = TVs z'" and [simp]: "TVs t = TVs t'"
    
  shows "[x \<leadsto> y @ z @ t] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> v] \<parallel> [t' \<leadsto> w] = [x \<leadsto> Subst y' y u @ Subst z' z v @ Subst t' t w]"
proof -
  have [simp]: "[x \<leadsto> y @ z @ t] = [x \<leadsto> y @ x] oo [y' \<leadsto> y'] \<parallel> [x \<leadsto> z @ t]"
    by (subst switch_par_comp_Subst, simp_all add:)
    show "[x \<leadsto> y @ z @ t] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> v] \<parallel> [t' \<leadsto> w] = [x \<leadsto> Subst y' y u @ Subst z' z v @ Subst t' t w]"     
      apply simp
      apply (subst comp_assoc, simp_all add: par_assoc)
      apply (subst comp_parallel_distrib, simp_all)
      apply (simp add: switch_par_comp_Subst)
      apply (subst switch_par_comp_Subst, simp_all, safe)
      apply (metis Subst_set_incl assms(12) assms(6) assms(9) contra_subsetD length_TVs)
      by (metis Subst_set_incl assms(10) assms(13) assms(7) length_TVs subsetCE)
  qed
    
    
lemma Comp_assoc_single: "length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 \<Longrightarrow> out A \<noteq> out B \<Longrightarrow> io_diagram A 
  \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> out B \<notin> set (In A) \<Longrightarrow>
    deterministic (Trs A) \<Longrightarrow>
    out A \<in> set (In B) \<Longrightarrow> out A \<in> set (In C) \<Longrightarrow> out B \<in> set (In C) \<Longrightarrow> (A ;; (B ;; C)) = (A ;; B ;; (A ;; C))"
  
  apply (simp add: Comp_def Let_def Var_def , safe)
    (* using [[simp_trace=true]] *)
      apply (simp add: Out_out, safe)
             apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym])
      
            apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym])
      
           apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym] )
      
          apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym])
 
      apply (simp add: Out_out, safe)
      apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym AAA_c addvars_assoc [THEN sym] )
      
   apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame  AAA_c diff_eq diff_addvars )
    
  apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym diff_inter_left diff_inter_right addvars_assoc [THEN sym])
  apply (simp add: Out_out par_empty_left par_empty_right set_diff set_inter set_addvars)
  apply (simp add:  Out_out comp_assoc [THEN sym])
   apply (subgoal_tac " [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    Trs A \<parallel> [(In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out A # ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In B \<oplus> (In C \<ominus> [out B])] oo
    [In B \<oplus> (In C \<ominus> [out B]) \<leadsto> In B @ (In C \<ominus> [out B])] oo
    Trs B \<parallel> [In C \<ominus> [out B] \<leadsto> In C \<ominus> [out B] ] oo
    [out B # (In C \<ominus> [out B]) \<leadsto> In C]
    =
    [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
    [(In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out B # ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In A \<oplus> (In C \<ominus> [out A])] oo
    [In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo
    Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo
    [out A # (In C \<ominus> [out A]) \<leadsto> In C] ")
   apply simp
proof -
  assume [simp]: "length (Out A) = Suc 0"
  assume [simp]: "length (Out B) = Suc 0"
  assume Diff[simp]: "out A \<noteq> out B"
  assume [simp]: "io_diagram A"
  assume [simp]: "io_diagram B"
  assume [simp]: "io_diagram C"
  assume [simp]: "out A \<in> set (In B)"
  assume [simp]: "out A \<in> set (In C)"
  assume [simp]: "out B \<in> set (In C)"
  assume "out B \<notin> set (In A)"
  assume det: "deterministic (Trs A)"
    
    have [simp]: " perm (In C \<ominus> [out A] \<ominus> [out B] \<ominus> (In B \<ominus> [out A])) (In C \<ominus> [out B] \<ominus> In B)"
              proof -
          have "In C \<ominus> [out B] \<ominus> [] \<ominus> out A # (In B \<ominus> [out A]) = In C \<ominus> [out B] \<ominus> [] \<ominus> In B"
            by (meson BaseOperationFeedbacklessVars.diff_eq_set_right BaseOperationFeedbacklessVars.io_diagram_distinct(1) BaseOperationFeedbacklessVars_axioms \<open>out A \<in> set (In B)\<close> \<open>io_diagram B\<close> perm_dist_mem perm_set_eq)
          then show "perm (In C \<ominus> [out A] \<ominus> [out B] \<ominus> (In B \<ominus> [out A])) (In C \<ominus> [out B] \<ominus> In B)"
            by (metis (no_types) diff_cons diff_sym perm_refl)
        qed
          
        define a where "a = out A"
        define b where "b = out B"
        define c where "c = out C"
        define x where "x = In A"
        define y where "y = In B"
        define z where "z = In C"
        have [simp]: "distinct x"
          by (simp add: x_def)
        have [simp]: "distinct y"
          by (simp add: y_def)
        have [simp]: "distinct z"
          by (simp add: z_def)
            
        have [simp]: "b \<in> set z"
          by (simp add: b_def z_def)
        have [simp]: "b \<noteq> a"
          using Diff a_def b_def by (simp del: Diff)
            
        have X: "b \<notin> set x"
          by (simp add: \<open>out B \<notin> set (In A)\<close> b_def x_def)

        have A_det: "Trs A oo [ [a] \<leadsto> [a,a] ] = [x\<leadsto> x @ x] oo Trs A \<parallel> Trs A"
          using det apply (subst deterministicE, simp_all add: x_def a_def)
          by (simp add: Out_out)
            
        define x' where "x' = newvars (x @ y @ z) (TVs x)"
          
        have [simp]: "set x' \<inter> set x = {}" and [simp]: "set x' \<inter> set y = {}" and [simp]: "set x' \<inter> set z = {}" and [simp]: "distinct x'"
            and [simp]: "TVs x' = TVs x"
          using x'_def and newvars_old_distinct [of "(x @ y @ z)" "(TVs x)"] by auto

   have A: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
        oo [a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] 
        oo [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])] 
        oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] 
        oo [b # (z \<ominus> [b]) \<leadsto> z] = 
    [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
        oo ([a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] 
        oo [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) 
        oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] 
        oo [b # (z \<ominus> [b]) \<leadsto> z]"
    by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
      
      have B: " ... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
        oo [a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
        oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] 
        oo [b # (z \<ominus> [b]) \<leadsto> z]"
        apply (subgoal_tac "([a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] 
        oo [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) = [a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]")
            apply simp
         apply (simp add:  a_def b_def c_def x_def y_def z_def)
        apply (subst switch_comp, simp_all)
         apply (simp add: set_diff set_addvars set_inter)
        apply (simp add: addvars_def)
        apply (subgoal_tac "perm ((out A # (In B \<ominus> [out A])) @ (In C \<ominus> [out A] \<ominus> [out B] \<ominus> (In B \<ominus> [out A]))) (In B @ (In C \<ominus> [out B] \<ominus> In B))")
          apply simp
          apply (rule perm_append)
         apply (simp add: perm_dist_mem)
        by simp
 
          
      have C: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
         oo ([x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])]
         oo [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x \<oplus> (z \<ominus> [a])] oo [x \<oplus> (z \<ominus> [a]) \<leadsto> x @ (z \<ominus> [a])] 
         oo Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] 
         oo [a # (z \<ominus> [a]) \<leadsto> z]
      =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
         oo ([x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])]
         oo ([b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x \<oplus> (z \<ominus> [a])] oo [x \<oplus> (z \<ominus> [a]) \<leadsto> x @ (z \<ominus> [a])])
         oo Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] 
         oo [a # (z \<ominus> [a]) \<leadsto> z]"
        by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
          
     have D: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
         oo ([x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])]
         oo [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])]
         oo Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] 
         oo [a # (z \<ominus> [a]) \<leadsto> z]"
       apply (subgoal_tac "([b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x \<oplus> (z \<ominus> [a])] oo [x \<oplus> (z \<ominus> [a]) \<leadsto> x @ (z \<ominus> [a])]) = [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])]")
        apply simp
       apply (subst switch_comp, simp_all, safe)
        apply (simp add: set_diff set_addvars )
       apply (rule perm_cons)
         apply (simp add: set_addvars set_diff)
        apply (simp add: addvars_diff)
       by (simp add: addvars_minus)
         
     have E: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    [x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
    oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     Trs B \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
       apply (subst par_id_comp, simp_all)
        apply (subst TO_comp, simp_all)
         apply (subst TO_comp, simp_all)
         apply (simp add: x_def)
         apply (simp add: a_def Out_out)
        apply (simp add: y_def)
       apply (subst par_id_comp, simp_all)
        apply (subst TO_comp, simp_all)
         apply (simp add: x_def)
         apply (simp add: a_def Out_out)
       apply (subst par_id_comp, simp_all)
         apply (simp add: x_def)
         by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
     have F: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))]
    oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     Trs B \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
         apply (subgoal_tac " [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    [x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] = 
      [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))]")
        apply simp
       apply (subst switch_par_comp, simp_all)
       by (auto simp add: set_addvars set_diff)
         
     have "[b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] = 
        [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> (b # x) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [x \<leadsto> x] \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])]"
       apply (subst switch_par_comp, simp_all add: set_addvars set_diff X)
         apply auto [2]
       apply (subst switch_par_comp, simp_all add: set_addvars set_diff X)
         by auto
         
    from this have "Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z] =  
    (Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> (b # x) @ (z \<ominus> [a] \<ominus> [b])]) 
    oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo ([x \<leadsto> x] \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ]) oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply simp
      by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
    also have "... =  (Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [ [b] \<leadsto> [b] ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply (subst comp_parallel_distrib)
        apply (simp_all add: x_def)
      apply (subst (2) par_switch, simp_all)
      apply (simp add: set_addvars set_diff)
      using X x_def by auto
    also have "... =  
    ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply (subgoal_tac "Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [ [b] \<leadsto> [b] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]
        =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) ))")
          apply simp
      apply (subst comp_parallel_distrib)
        apply (simp_all add: b_def Out_out)
      apply (subst comp_parallel_distrib)
        apply (simp_all add: y_def Out_out)
      apply (subst switch_par_comp)
      by (simp_all add: set_diff set_addvars)
    
    also have "... =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    (Trs A \<parallel> [ b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])]) oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply (subgoal_tac " Trs A \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [a] ] =  (Trs A \<parallel> [ b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])])")
       apply simp
        apply (subst comp_parallel_distrib)
        apply (simp_all add: a_def Out_out)
      by (subst switch_comp, simp_all add: set_diff, auto)
    also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [ b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])]) oo ([ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    [a # (z \<ominus> [a]) \<leadsto> z])"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)

    also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> ([ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])])) oo ([a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a]) ] oo
    [a # (z \<ominus> [a]) \<leadsto> z])"
      apply (subgoal_tac "[ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] = [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a]) ]")
       apply simp
       apply (subgoal_tac "[b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])] = [ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]")
        apply simp
        apply (subst par_switch, simp_all add: set_diff)
      apply (subst par_switch, simp_all add: set_diff)
      using Diff a_def b_def by auto
        
    also have "... =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> ([ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])])) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
      apply (subgoal_tac " ([a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a]) ] oo [a # (z \<ominus> [a]) \<leadsto> z]) = [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]")
        apply simp
        apply (subst switch_comp, simp_all add: set_diff)
      using Diff a_def b_def apply simp
       apply (metis \<open>b \<noteq> a\<close> \<open>distinct z\<close> \<open>out A \<in> set (In C)\<close> \<open>out B \<in> set (In C)\<close> a_def b_def distinct_diff perm_dist_mem perm_set_eq set_ConsD z_def)
      by blast
    also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
      by (simp add: par_assoc)
     also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
    oo (([b # x  \<leadsto> x @ [b] ] oo Trs A \<parallel> [ [b] \<leadsto> [b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
       apply (subgoal_tac " ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]) =  (([b # x  \<leadsto> x @ [b] ] oo Trs A \<parallel> [ [b] \<leadsto> [b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])")
        apply simp
        apply (subst comp_parallel_distrib)
        by (simp_all add: x_def)
     also have "... =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
    oo (([ [b] \<leadsto> [b] ] \<parallel> Trs A oo [ [b,a] \<leadsto> [a,b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
       apply (subgoal_tac "([b # x  \<leadsto> x @ [b] ] oo Trs A \<parallel> [ [b] \<leadsto> [b] ]) = ([ [b] \<leadsto> [b] ] \<parallel> Trs A oo [ [b,a] \<leadsto> [a,b] ])")
        apply simp
         thm switch_parallel_a
         apply (cut_tac x= "[b]" and y = x and u = "[b]" and v = "[a]" and T = "Trs A" and S = "[ [b] \<leadsto> [b] ]" in switch_parallel_a)
               apply (simp_all)
           apply (simp add: X)
           by (simp_all add: x_def a_def Out_out)
      also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
    oo ([ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
        apply (subgoal_tac "(([ [b] \<leadsto> [b] ] \<parallel> Trs A oo [ [b,a] \<leadsto> [a,b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
          = ([ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])")
         apply simp
        apply (subst comp_parallel_distrib)
        by (simp_all add: a_def Out_out)
     also have "... =  [ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
    oo [ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo ([ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z])"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         also have "... = [ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
             oo ([ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z])"
        apply (subgoal_tac " (Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
    oo [ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) = Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
            apply simp
             apply (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out)
           by (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out)
             
    also have "... = [ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
             oo [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
      
      apply (subgoal_tac " ([ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]) = [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]")
       apply (simp)
      apply (subst par_switch, simp_all add: set_diff)
      apply (subst switch_comp, simp_all add: set_diff)
       apply (simp add: perm_mset)
        by blast
        

    finally have Aa: "Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z] =  
    [y \<leadsto> y] \<parallel> [(x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
      by simp

     have G: " [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z] =  
    [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    (Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z])"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
     have H: "... =   [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [(x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
      apply (simp add: Aa)
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
       
     have I:"[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] = 
        [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         
    have J:"... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
      apply (subgoal_tac " ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) = [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]")
          apply simp
      by (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out)
        have K:"... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          apply (simp add: par_assoc)
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        have L:"... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo  [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
        Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
       apply (subgoal_tac "((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) =  (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo  [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]")
           apply simp
      by (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out a_def)
            

    have Ba: "[a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])] = 
        [ [a] \<leadsto> [a,a] ] \<parallel>  [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
          oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ [a]  ] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
          oo [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]"
      apply (subst par_switch, simp_all add: set_diff set_addvars)
        apply (cut_tac x = "a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))" and y = "[a]" and y' = "[a]" 
          and z = "a # (y \<ominus> [a])" and z' = " (y \<ominus> [a]) @ [a]" and u = "z \<ominus> [a] \<ominus> [b] " and u' = "z \<ominus> [a] \<ominus> [b]"  in switch_par_comp3)
                  apply (simp_all add: set_diff set_addvars)
        apply auto
      apply (cut_tac x = "a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))" 
          and y = "a # (y \<ominus> [a])" and y' = y and z = "a # (z \<ominus> [a] \<ominus> [b])" and z' = "z \<ominus> [b]"  in switch_par_comp)
      by (simp_all add:set_diff set_addvars, auto)
        
    have Ca: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    ([ [a] \<leadsto> [a, a] ] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
     [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]) oo
    Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo
    [b # (z \<ominus> [b]) \<leadsto> z] = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [ [a] \<leadsto> [a, a] ] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
     ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo
    Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo
    [b # (z \<ominus> [b]) \<leadsto> z])"
      by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
    have Da: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z])"
      apply (subgoal_tac " (Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a, a] ] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) = 
        (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]")
       apply simp
      by (subst comp_parallel_distrib, simp_all add: a_def Out_out)
        
    have Ea: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        (([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]  oo [b # (z \<ominus> [b]) \<leadsto> z])"
      apply (subgoal_tac "[a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] = ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]")
       apply simp
      by (subst comp_parallel_distrib, simp_all add: y_def)
    have Fa: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        (([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo [ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z])"
      apply (subgoal_tac "([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] 
          = ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo [ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] ")
       apply simp
      apply (subst comp_parallel_distrib, simp_all)
       apply (subst TO_comp, simp_all add: y_def b_def Out_out)
      by (subst switch_comp, simp_all add: set_diff, auto)
        
     have Ga: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo ([ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z])"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         have Ha: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo ([ b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
           apply (subgoal_tac " ([ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z]) = ([ b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])")
            apply simp
           apply (subst par_switch, simp_all add:set_diff, auto)
           apply (subst switch_comp, simp_all add: set_diff)
            apply (rule set_perm , simp_all add: set_diff, auto)
           using a_def z_def apply auto[1]
           using \<open>b \<noteq> a\<close> by auto
             
       
         have Ab: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo ([x \<leadsto> x @ x] oo Trs A \<parallel> Trs A) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]
        = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (([x \<leadsto> x @ x] oo Trs A \<parallel> Trs A) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])])"
           by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         have Ac: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo 
            (([x \<leadsto> x @ x] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> Trs A \<parallel> ([(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])])))"
           apply (subgoal_tac "(([x \<leadsto> x @ x] oo Trs A \<parallel> Trs A) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) = 
               (([x \<leadsto> x @ x] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> Trs A \<parallel> ([(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])])))")
            apply simp
           apply (subst comp_parallel_distrib, simp_all)
            apply (simp add: x_def)
           by (subst switch_par_comp, simp_all)
         have Ad: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo 
            [x \<leadsto> x @ x] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> Trs A \<parallel> [(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])]"
           by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def par_assoc)
         have Ae: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ ((y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> Trs A \<parallel> [(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])]"
           by (subst switch_par_comp, simp_all add: set_addvars set_diff, auto)
           
           
         have "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
              oo Trs A \<parallel> Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
              = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo (Trs A \<parallel> (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
            ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
           apply (simp add: par_assoc)
           by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo Trs A \<parallel> (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
          
           apply (subst comp_parallel_distrib, simp_all add: a_def Out_out)
          by (subst comp_parallel_distrib, simp_all add: a_def Out_out)
            
         also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo Trs A \<parallel> ([ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] oo [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
           apply (subgoal_tac "(Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ]) 
            = ([ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] oo [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A)")
            apply simp
           apply (subst switch_parallel_a [THEN sym], simp_all add: set_diff)
           using \<open>set x' \<inter> (set y) = {}\<close> apply blast
           by (simp_all add: Out_out a_def x_def)
             
        also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo ([x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
                    oo  Trs A \<parallel> ([y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
          apply (subgoal_tac " Trs A \<parallel> ([ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] oo [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
              = ([x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
                    oo  Trs A \<parallel> ([y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])")
           apply simp
           apply (subst comp_parallel_distrib, simp_all add: a_def Out_out x_def)
          by (subst comp_parallel_distrib, simp_all add: x_def)
            also have "... = ([x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo [x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
                    oo  ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])])"
           apply (simp add: par_assoc)
              by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
                
          also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] 
                    oo  ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])])"
            
           apply (subgoal_tac "([x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (x @ (y \<ominus> [a])) @ (z \<ominus> [a] \<ominus> [b])] 
                oo [x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
              = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] ")
             apply simp
            apply (subst switch_par_comp_Subst3, simp_all add: set_diff set_addvars)
              apply (simp add: Diff_Int_distrib, blast)
            apply (subgoal_tac " Subst (x' @ (y \<ominus> [a])) (x @ (y \<ominus> [a])) ((y \<ominus> [a]) @ x') = (y \<ominus> [a]) @ x")
             apply simp
            apply (simp add: Subst_append, safe)
             apply (metis (no_types, lifting) AAA_c Subst_eq Subst_not_in_a TVs_length_eq \<open>TVs x' = TVs x\<close> \<open>set x' \<inter> set y = {}\<close> disjoint_insert(2) empty_set insert_Diff list.simps(15) set_diff)
            by (metis Subst_all Subst_cancel_left_type TVs_length_eq \<open>TVs x' = TVs x\<close> \<open>set x' \<inter> set y = {}\<close> empty_inter_diff empty_set newvars_distinct set_inter x'_def)
              
        also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] 
                    oo  (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
          
          apply (subst comp_parallel_distrib)
            apply (simp_all add: y_def a_def Out_out)[2]
          apply (subst comp_switch_id)
            apply (simp_all add: set_diff a_def Out_out) [2]
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
            
       finally have Bc: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
              oo Trs A \<parallel> Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]
            = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] 
                    oo  (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
         by simp
           
              
     have "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] = 
        [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
        ([x \<leadsto> x] \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> ([x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])])) oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]"
       apply (subgoal_tac " (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] = 
          ([x \<leadsto> x] \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> ([x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]))")
        apply simp
       apply (subst comp_parallel_distrib)
         apply (simp_all add: x_def y_def a_def Out_out) [2]
       apply (simp add: distinct_id)
       by (subst comp_id_left_simp, simp_all add: x_def a_def Out_out)
     also have " ... =  ([x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
        [x \<leadsto> x] \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo
    ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
       apply (simp add: par_assoc)
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
     also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] oo
    ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
       by (subst switch_par_comp3, simp_all add: set_diff set_addvars, auto)
         
    also have "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]"
      apply (subst comp_parallel_distrib)
        apply (simp_all add: Out_out a_def b_def c_def x_def y_def z_def) [2]
      apply (subst comp_parallel_distrib)
        apply (simp_all add: Out_out a_def b_def c_def x_def y_def z_def) [2]
      by (simp add: x_def)
        
    finally have Cc: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]"
      by simp
         
     show "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    Trs A \<parallel> [(In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out A # ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In B \<oplus> (In C \<ominus> [out B])] oo
    [In B \<oplus> (In C \<ominus> [out B]) \<leadsto> In B @ (In C \<ominus> [out B])] oo
    Trs B \<parallel> [In C \<ominus> [out B] \<leadsto> In C \<ominus> [out B] ] oo
    [out B # (In C \<ominus> [out B]) \<leadsto> In C] =
    [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
    [(In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out B # ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In A \<oplus> (In C \<ominus> [out A])] oo
    [In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo
    Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo
    [out A # (In C \<ominus> [out A]) \<leadsto> In C]"
       apply (simp add: a_def [THEN sym] b_def [THEN sym] c_def [THEN sym] x_def [THEN sym] y_def [THEN sym] z_def [THEN sym])
       apply (simp add: A B C D E F)
       apply (simp add: X AAA_c)
       apply (simp add: G H I J K L)
       apply (simp add: Ba )
       apply (simp add: Ca Da Ea Fa Ga Ha)
         thm arg_cong
       apply (subst  arg_cong [of _ _ "\<lambda> A . A oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"], simp_all)
       apply (simp add: A_det)
       apply (subst Ab)
         apply (simp add: Ac Ad Ae)
         apply (simp add: Bc Cc)
         by (simp add: par_assoc)
     qed
         
lemma Comp_commute_aux:
  assumes [simp]: "length (Out A) = 1"
    and [simp]: "length (Out B) = 1"
    and [simp]: "io_diagram A"
    and [simp]: "io_diagram B"
    and [simp]: "io_diagram C"
    and [simp]: "out B \<notin> set (In A)"
    and [simp]: "out A \<notin> set (In B)"
    and [simp]: "out A \<in> set (In C)"
    and [simp]: "out B \<in> set (In C)"
    and Diff: "out A \<noteq> out B"

    shows "Trs (A ;; (B ;; C)) = 
                [In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ In B @ (In C \<ominus> [out A] \<ominus> [out B])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ In C \<ominus> [out A] \<ominus> [out B] \<leadsto> In C \<ominus> [out A] \<ominus> [out B] ]
                    oo [out A # out B # (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In C] 
                    oo Trs C"
      and "In (A ;; (B ;; C)) = In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B])"
      and "Out (A ;; (B ;; C)) = Out C"
    proof -
        define a where "a = out A"
        define b where "b = out B"
        define c where "c = out C"
        define x where "x = In A"
        define y where "y = In B"
        define z where "z = In C"
        have [simp]: "distinct x"
          by (simp add: x_def)
        have [simp]: "distinct y"
          by (simp add: y_def)
        have [simp]: "distinct z"
          by (simp add: z_def)
            
        have [simp]: "b \<in> set z"
          by (simp add: b_def z_def)
        have [simp]: "b \<noteq> a"
          using Diff a_def b_def by (simp)
        have [simp]: "a \<noteq> b"
          using Diff a_def b_def by (simp)
        have [simp]: "b \<notin> set x"
          by (simp add: b_def x_def)
            
        have [simp]: "a \<notin> set y"
          by (simp add: a_def y_def)
            
        have [simp]: "a \<in> set z"
          by (simp add: \<open>a \<equiv> out A\<close> \<open>z \<equiv> In C\<close>)
            
        have [simp]: "(y \<oplus> (z \<ominus> [b])) \<ominus> [a] = y \<oplus> (z \<ominus> [a] \<ominus> [b])"
          by (simp add: AAA_c addvars_minus diff_sym)
            
            
        have "[y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] 
            = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo ([y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo ([y @ [a] \<leadsto> a # y] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          apply (subgoal_tac " ([y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) = 
                ([y @ [a] \<leadsto> a # y] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
           apply simp
          by (subst comp_parallel_distrib, simp_all add: y_def)
          also have "... = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo (Trs B \<parallel> [ [a] \<leadsto> [a] ] oo [ [b, a] \<leadsto> [a, b] ])  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
            apply (subgoal_tac "([y @ [a] \<leadsto> a # y] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B)  = (Trs B \<parallel> [ [a] \<leadsto> [a] ] oo [ [b, a] \<leadsto> [a, b] ])")
             apply simp
            thm switch_parallel_a
            apply (cut_tac switch_parallel_a [of y "[a]" "[b]" "[a]" "Trs B" "[ [a] \<leadsto> [a] ]"])
                  apply simp_all
             by (simp_all add: y_def b_def Out_out)
              also have "... =  [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo (Trs B \<parallel> [ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
                apply (subgoal_tac "(Trs B \<parallel> [ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
                    =   (Trs B \<parallel> [ [a] \<leadsto> [a] ] oo [ [b, a] \<leadsto> [a, b] ])  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
                apply simp
                by (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out)
          also have "... = ([y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo Trs B \<parallel> ([ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])) oo ([ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
            apply (simp add: par_assoc)
            by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
              also have "... =  Trs B \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo  ([ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
                apply (subgoal_tac "([y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo Trs B \<parallel> ([ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])) = Trs B \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] ")
                 apply simp
                apply (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out)
                by (subst par_switch, simp_all add: set_diff)
        also have "... =  Trs B \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          apply (subst par_switch)
             apply (simp_all add: set_diff)
          apply (subst switch_comp, simp_all add: set_diff)
          by (subst set_perm, simp_all add: set_diff, auto)
        also have "... =  (Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [ [b] \<leadsto> [b] ] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])])oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          by (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out)
        also have "... = Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo ([ [b] \<leadsto> [b] ] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... = Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z]"
          apply (subst par_switch, simp_all add: set_diff, auto)
          apply (subst switch_comp, simp_all add: set_diff, auto)
          by (rule set_perm, simp_all add: set_diff, auto)
            
        finally have Aa: "Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]" (is "?X = ?Y")
          by simp
            
        have "Trs (A ;; (B ;; C)) = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] oo
            ([y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])] oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] oo Trs C  )"       
          by (simp add: Comp_def Let_def a_def [THEN sym] x_def [THEN sym] b_def [THEN sym] y_def [THEN sym]
              c_def [THEN sym] z_def [THEN sym] Var_def Out_out par_empty_left set_addvars set_diff addvars_assoc [THEN sym])
        also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo ([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] oo
            [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] oo Trs C"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
            also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
                  oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] oo Trs C"
              apply (subgoal_tac "([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] oo
            [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) = [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]")
               apply simp
              apply (subst switch_comp)
                 apply (simp_all add: set_addvars set_diff)
              by (subst set_perm, simp_all add: set_addvars set_diff, auto)
          also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
                  oo (Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z]) oo Trs C"
            by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
          also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
                  oo ?Y oo Trs C"
            by (simp add: Aa)
          also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo ([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])] oo
                [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
            by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
           also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  a # y @ (z \<ominus> [a] \<ominus> [b]) ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
            apply (subgoal_tac "([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])] oo
                [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])  = 
                [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  a # y @ (z \<ominus> [a] \<ominus> [b]) ]")
              apply (simp)
             apply (subst switch_par_comp, simp_all add: set_diff set_addvars, auto)
               thm switch_par_comp
               apply (cut_tac switch_par_comp [of "a # (y \<oplus> (z \<ominus> [a] \<ominus> [b]))" " y @ [a]" "(z \<ominus> [a] \<ominus> [b])" "a # y"])
                      apply simp
               by (simp_all add: set_addvars set_diff, auto)
             
            also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [ [a] \<leadsto> [a] ] \<parallel> [(y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  y @ (z \<ominus> [a] \<ominus> [b]) ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
              apply (subst par_switch)
              by (simp_all add: set_diff set_addvars)
                also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [ [a] \<leadsto> [a] ] \<parallel> [(y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  y @ (z \<ominus> [a] \<ominus> [b]) ])
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                  by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
              also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] 
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                apply (subgoal_tac "(Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [ [a] \<leadsto> [a] ] \<parallel> [(y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  y @ (z \<ominus> [a] \<ominus> [b]) ]) =  Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] ")
                 apply simp
                by (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out a_def)
                  
                  
              also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
                  oo ([x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> ( [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]))
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                
                apply (subgoal_tac "Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])]  = ([x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> ( [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]))")
                 apply simp
                apply (subst comp_parallel_distrib)
                  apply (simp_all add: y_def b_def Out_out x_def) [2]
                by (subst switch_par_comp, simp_all add: x_def)
               also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
                  oo [x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                apply (simp add: par_assoc) 
                 by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
            also have "... =  ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
              apply (subgoal_tac " ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
                  oo [x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])]) = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])]) ")
              apply simp
              by (subst switch_par_comp, simp_all add: set_diff set_addvars, auto)
           also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])]) oo Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                apply (subgoal_tac " (Trs A \<parallel> [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) =  Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
              apply simp
                apply (subst comp_parallel_distrib)
                  apply (simp_all add: y_def b_def Out_out x_def a_def)
             by (subst comp_parallel_distrib, simp_all add: Out_out)
        
           finally have "Trs (A ;; (B ;; C)) = 
                [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                    oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] 
                    oo Trs C"
             by simp
               
        from this show "Trs (A ;; (B ;; C)) = 
                [In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ In B @ (In C \<ominus> [out A] \<ominus> [out B])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ In C \<ominus> [out A] \<ominus> [out B] \<leadsto> In C \<ominus> [out A] \<ominus> [out B] ]
                    oo [out A # out B # (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In C] 
                    oo Trs C"
          by (simp add: x_def y_def z_def a_def b_def)
        show "In (A ;; (B ;; C)) = In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B])"
          apply (simp add: Comp_def Let_def Var_def Out_out set_addvars set_diff, safe)
           apply (metis \<open>a \<equiv> out A\<close> \<open>b \<equiv> out B\<close> \<open>y \<oplus> (z \<ominus> [b]) \<ominus> [a] = y \<oplus> (z \<ominus> [a] \<ominus> [b])\<close> addvars_assoc b_def y_def z_def) 
            by (simp add: Diff)
          
      show  "Out (A ;; (B ;; C)) = Out C"
          apply (simp add: Comp_def Let_def Var_def Out_out set_addvars set_diff, safe)
            by (simp add: Diff)
  qed

       
lemma Comp_commute:
  assumes [simp]: "length (Out A) = 1"
    and [simp]: "length (Out B) = 1"
    and [simp]: "io_diagram A"
    and [simp]: "io_diagram B"
    and [simp]: "io_diagram C"
    and [simp]: "out B \<notin> set (In A)"
    and [simp]: "out A \<notin> set (In B)"
    and [simp]: "out A \<in> set (In C)"
    and [simp]: "out B \<in> set (In C)"
    and Diff: "out A \<noteq> out B"
  shows "in_equiv (A ;; (B ;; C)) (B ;; (A ;; C))"
    proof -
        define a where "a = out A"
        define b where "b = out B"
        define c where "c = out C"
        define x where "x = In A"
        define y where "y = In B"
        define z where "z = In C"
        have [simp]: "distinct x"
          by (simp add: x_def)
        have [simp]: "distinct y"
          by (simp add: y_def)
        have [simp]: "distinct z"
          by (simp add: z_def)
            
        have [simp]: "b \<in> set z"
          by (simp add: b_def z_def)
        have [simp]: "b \<noteq> a"
          using Diff a_def b_def by (simp)
        have [simp]: "a \<noteq> b"
          using Diff a_def b_def by (simp)
        have [simp]: "b \<notin> set x"
          by (simp add: b_def x_def)
            
        have [simp]: "a \<notin> set y"
          by (simp add: a_def y_def)
            
        have [simp]: "a \<in> set z"
          by (simp add: \<open>a \<equiv> out A\<close> \<open>z \<equiv> In C\<close>)
            
        have [simp]: "(y \<oplus> (z \<ominus> [b])) \<ominus> [a] = y \<oplus> (z \<ominus> [a] \<ominus> [b])"
          by (simp add: AAA_c addvars_minus diff_sym)
            
        
        have A: "Trs (A ;; (B ;; C)) = 
                [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                    oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] 
                    oo Trs C"
          apply (subst Comp_commute_aux, simp_all)
           apply (simp add: Diff)
          by (simp add: x_def y_def z_def a_def b_def)
            
            
        define x' where "x' = newvars (y) (TVs x)"
          
        have [simp]: "distinct x'" and [simp]: "set y \<inter> set x' = {}"
           by (simp_all add: x'_def)
            
            
        have  " [In (A ;; (B ;; C)) \<leadsto> In (B ;; (A ;; C))] oo Trs (B ;; (A ;; C)) = 
              [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a])]
              oo ([y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])] 
              oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C)"
          apply (subst Comp_commute_aux, simp_all)
          using Diff apply auto
          apply (subst Comp_commute_aux, simp_all)
          apply (subst Comp_commute_aux, simp_all)
          by (simp add: x_def[THEN sym] y_def[THEN sym] z_def[THEN sym] a_def[THEN sym] b_def[THEN sym])
            
        also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a])]
              oo [y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... =  ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          apply (subst switch_comp, simp_all)
          by (rule set_perm, simp_all add: set_addvars set_diff, auto)
            also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo ([y @ x' \<leadsto> x' @ y] oo Trs A \<parallel> Trs B oo [ [a, b] \<leadsto> [b, a] ]) \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
              
              apply (subgoal_tac "Trs B \<parallel> Trs A = ([y @ x' \<leadsto> x' @ y] oo Trs A \<parallel> Trs B oo [ [a] @ [b] \<leadsto> [b] @ [a] ])")
               apply simp
              apply (subst switch_par [THEN sym], simp_all)
              by (simp_all add: y_def x'_def x_def b_def a_def Out_out)
        also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo ([y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo [ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          
          apply (subgoal_tac "([y @ x' \<leadsto> x' @ y] oo Trs A \<parallel> Trs B oo [ [a, b] \<leadsto> [b, a] ]) \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]  = 
               ([y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo [ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) ")
           apply simp
          apply (subst comp_parallel_distrib)
            apply (simp_all add: Out_out x'_def x_def y_def) [2]
          apply (subst comp_parallel_distrib)
          by (simp_all add: Out_out x'_def x_def y_def b_def a_def)
            
        also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])]
              oo [y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo ([ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]) oo Trs C"
          by (simp add:  Out_out comp_assoc a_def b_def x_def y_def z_def x'_def)
        also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [b] \<ominus> [a])]
               oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo ([ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]) oo Trs C"
          apply (subgoal_tac "([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y @ x) @ (z \<ominus> [b] \<ominus> [a])]
              oo [y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [b] \<ominus> [a])]")
           apply simp
            thm switch_par_comp_Subst
            apply (subst switch_par_comp_Subst)
                     apply (simp_all add: set_addvars set_diff, auto) [9]
             apply (simp add: x'_def)
            apply (simp add: Subst_append)
              apply (subgoal_tac "Subst (y @ x') (y @ x) x' = x")
             apply (subgoal_tac "Subst (y @ x') (y @ x) y = y")
              apply simp
             apply (metis Subst_eq Subst_not_in \<open>distinct x'\<close> \<open>distinct y\<close> \<open>set y \<inter> set x' = {}\<close> dist_perm distinct_append length_Subst perm_tp)
              by (simp add: \<open>x' \<equiv> newvars y (TVs x)\<close>)
            
        also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [b] \<ominus> [a])]
               oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [a # b # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          apply (subgoal_tac "([ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]) = [a # b # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]")
           apply simp
          apply (subst par_switch, simp_all add: set_diff)
          apply (subst switch_comp, simp_all add: set_addvars set_diff)
          by (rule set_perm, auto simp add: set_diff)
        also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
          by (simp add: diff_sym)
          
            
        finally have [simp]: "Trs (A ;; (B ;; C)) = [In (A ;; (B ;; C)) \<leadsto> In (B ;; (A ;; C))] oo Trs (B ;; (A ;; C))"
          apply (simp)
          by (simp add: A)
            
        have [simp]: "Out (A ;; (B ;; C)) = Out (B ;; (A ;; C))"
          apply (subst Comp_commute_aux, simp_all)
           apply (simp add: Diff)
          apply (subst Comp_commute_aux, simp_all)
           using Diff by auto
            
        have [simp]: "perm (In (A ;; (B ;; C))) (In (B ;; (A ;; C)))"
          apply (subst Comp_commute_aux, simp_all)
           apply (simp add: Diff)
          apply (subst Comp_commute_aux, simp_all)
          using Diff apply auto
            by (simp add: diff_sym distinct_perm_switch)

        show "in_equiv (A ;; (B ;; C)) (B ;; (A ;; C))"
          by (simp add: in_equiv_def)
  qed

lemma CompA_commute_aux_a: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 
    \<Longrightarrow> out A \<notin> set (Out C) \<Longrightarrow> out B \<notin> set (Out C)
    \<Longrightarrow> out A \<noteq> out B \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A)
    \<Longrightarrow> deterministic (Trs A)
    \<Longrightarrow> (CompA (CompA B A) (CompA B C)) = (CompA (CompA A B) (CompA A C))"
  proof -
    assume [simp]: "io_diagram A"
    assume [simp]: "io_diagram B"
    assume [simp]: "io_diagram C"
    assume "length (Out A) = 1"
    assume "length (Out B) = 1"
    assume [simp]: "out A \<notin> set (Out C)"
    assume [simp]: "out B \<notin> set (Out C)"
    assume B: "out A \<noteq> out B"
    assume [simp]: "deterministic (Trs A)"
      
    have [simp]: "Out A = [out A]"
      using Out_out \<open>length (Out A) = 1\<close> by auto
    have [simp]: "Out B = [out B]"
      using Out_out \<open>length (Out B) = 1\<close> by auto
    have [simp]: "io_diagram (A ;; C)"
      by (rule io_diagram_Comp, simp_all)
    assume A[simp]: "out A \<in> set (In B)"
    assume [simp]: "out B \<notin> set (In A)"
      
    have [simp]: "io_diagram (B ;; C)"
      by (rule io_diagram_Comp, simp_all)
    have [simp]: "io_diagram (A ;; (B ;; C))"
      apply (rule io_diagram_Comp, simp_all)
      by (simp add: Comp_def Let_def Var_def set_addvars set_diff)
    then show ?thesis
      apply (simp)
        proof (cases "out A \<in> set (In C)")
          case True
          from True have [simp]: "out A \<in> set (In C)"
            by simp
          have [simp]: "out A \<in> set (In (CompA B C))"
            by (simp add: In_CompA set_addvars)
          then show "(CompA A (CompA B C)) = (CompA (A ;; B) (CompA A C))"
            apply (simp)
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out ((A ;; B)) \<in> set (In (A ;; C))"
              apply (simp)
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def True)
            then show "(A ;; CompA B C) = (CompA (A ;; B) (A ;; C))" 
              apply (simp add: True)
              apply (rule  Comp_assoc_single, simp_all)
              using B apply blast
                using True by blast
          next
            case False
            have [simp]: "out ((A ;; B)) \<notin> set (In (A ;; C))"
              apply (simp)
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def False)
            then show "(A ;; CompA B C) = (CompA (A ;; B) (A ;; C))"
              by (simp add: False)
          qed
        next
          case False
          assume [simp]: "out A \<notin> set (In C)"
          then show "(CompA A (CompA B C)) = (CompA (A ;; B) (CompA A C))"
            apply simp
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out (A ;; B) \<in> set (In C)"
              by (simp add: True)
            have [simp]: "out A \<in> set (In (B ;; C))"
              by (simp add: Comp_def Let_def set_addvars)
            then show "(CompA A (CompA B C)) = (CompA (A ;; B) C)" 
              by (simp add: True Comp_assoc_new in_equiv_eq)
          next
            case False
            have [simp]: "out (A ;; B) \<notin> set (In C)"
              using False by simp
            then show "(CompA A (CompA B C)) = (CompA (A ;; B) C)" 
              by (simp add: False in_equiv_eq)
          qed
        qed
  qed

    
lemma CompA_commute_aux_b: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 
    \<Longrightarrow> out A \<notin> set (Out C) \<Longrightarrow> out B \<notin> set (Out C)
    \<Longrightarrow> out A \<noteq> out B \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> out B \<notin> set (In A)
    \<Longrightarrow> in_equiv (CompA (CompA B A) (CompA B C)) (CompA (CompA A B) (CompA A C))"
  proof -
    assume [simp]: "io_diagram A"
    assume [simp]: "io_diagram B"
    assume [simp]: "io_diagram C"
    assume "length (Out A) = 1"
    assume "length (Out B) = 1"
    assume [simp]: "out A \<notin> set (Out C)"
    assume [simp]: "out B \<notin> set (Out C)"
    assume B: "out A \<noteq> out B"
      
    have [simp]: "Out A = [out A]"
      using Out_out \<open>length (Out A) = 1\<close> by auto
    have [simp]: "Out B = [out B]"
      using Out_out \<open>length (Out B) = 1\<close> by auto
    have [simp]: "io_diagram (A ;; C)"
      by (rule io_diagram_Comp, simp_all)
        
    assume A[simp]: "out A \<notin> set (In B)"
    assume [simp]: "out B \<notin> set (In A)"
      
    have [simp]: "io_diagram (B ;; C)"
      by (rule io_diagram_Comp, simp_all)
        (*
    have [simp]: "io_diagram (A ;; (B ;; C))"
      apply (rule io_diagram_Comp_a, simp_all)
      by (simp add: Comp_def Let_def Var_def set_addvars set_diff)
*)
    then show ?thesis
      apply (simp)
        proof (cases "out A \<in> set (In C)")
          case True
          from True have [simp]: "out A \<in> set (In C)"
            by simp
          have [simp]: "out A \<in> set (In (CompA B C))"
            apply (simp add: In_CompA set_addvars set_diff)
              using B by blast
          then show "in_equiv (CompA A (CompA B C)) (CompA B (CompA A C))"
            apply (simp)
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out B \<in> set (In (A ;; C))"
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def True)
            then show "in_equiv (A ;; CompA B C) (CompA B (A ;; C))" 
              apply (simp add: True)
                thm Comp_commute
                apply (subst Comp_commute, simp_all)
                 apply (simp add: True)
                  by (simp add: B)
          next
            case False
            have [simp]: "out B \<notin> set (In (A ;; C))"
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def False)
            then show "in_equiv (A ;; CompA B C) (CompA B (A ;; C))"
              apply (simp add: False)
                by (simp add: in_equiv_eq)
          qed
        next
          case False
          assume [simp]: "out A \<notin> set (In C)"
          then show "in_equiv (CompA A (CompA B C)) (CompA B (CompA A C))"
            apply simp
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out B \<in> set (In C)"
              by (simp add: True)
            have [simp]: "out A \<notin> set (In (B ;; C))"
              by (simp add: Comp_def Let_def set_addvars set_diff)
            then show "in_equiv (CompA A (CompA B C))  (CompA B C)" 
              by (simp add: Comp_assoc_new in_equiv_eq)
          next
            case False
            have [simp]: "out B \<notin> set (In C)"
              using False by simp
            then show "in_equiv (CompA A (CompA B C)) (CompA B C)" 
              by (simp add: in_equiv_eq)
          qed
        qed
  qed

    
fun In_Equiv :: "(('var, 'a) Dgr) list \<Rightarrow> (('var, 'a) Dgr) list \<Rightarrow> bool" where 
  "In_Equiv [] [] = True" |
  "In_Equiv (A # As) (B# Bs) = (in_equiv A B \<and> In_Equiv As Bs)" |
  "In_Equiv _ _ = False"
  
thm internal_def
  
thm fb_out_less_step_def
thm fb_less_step_def
  
thm CompA_commute_aux_b
thm CompA_commute_aux_a
 
lemma CompA_commute: 
  assumes [simp]: "io_diagram A"
    and [simp]: "io_diagram B"
    and [simp]: "io_diagram C"
    and [simp]: "length (Out A) = 1"
    and [simp]: "length (Out B) = 1"
    and [simp]: "out A \<notin> set (Out C)"
    and [simp]: "out B \<notin> set (Out C)"
    and [simp]: "out A \<noteq> out B"
    and [simp]: "deterministic (Trs A)"
    and [simp]: "deterministic (Trs B)"
    and A: "(out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A))"
  shows "in_equiv (CompA (CompA B A) (CompA B C)) (CompA (CompA A B) (CompA A C))"
    proof (cases "out A \<in> set (In B)")
      case True
      from this and A have [simp]: "out B \<notin> set (In A)"
        by simp
      then show ?thesis
        using True apply (subst CompA_commute_aux_a, simp_all)
          apply (rule in_equiv_eq)
         apply (metis BBB_a BaseOperationFeedbacklessVars.CompA_in BaseOperationFeedbacklessVars_axioms True assms(1) assms(2) assms(3) assms(4) assms(5) io_diagram_CompA)
          by simp
    next
      case False
      then have [simp]: "out A \<notin> set (In B)"
        by simp
      show ?thesis
      proof (cases "out B \<in> set (In A)")
        case True
        then show ?thesis
          thm CompA_commute_aux_a
          apply (subst CompA_commute_aux_a [of B A], simp_all)
          using assms(8) apply fastforce
          by (metis BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.CompA_in BaseOperationFeedbacklessVars_axioms assms(1) assms(2) assms(3) assms(4) assms(5) in_equiv_eq io_diagram_CompA)
      next
        case False
        then show ?thesis
          thm CompA_commute_aux_b
          by (subst CompA_commute_aux_b, simp_all)
      qed
    qed
  
  
lemma In_Equiv_CompA_twice: "(\<And> C . C \<in> set As \<Longrightarrow> io_diagram C \<and> out A \<notin> set (Out C) \<and> out B \<notin> set (Out C)) \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B
    \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 \<Longrightarrow> out A \<noteq> out B
    \<Longrightarrow> deterministic (Trs A) \<Longrightarrow> deterministic (Trs B)
    \<Longrightarrow> (out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A))
    \<Longrightarrow> In_Equiv (map (CompA (CompA B A)) (map (CompA B) As)) (map (CompA (CompA A B)) (map (CompA A) As))"
  apply (induction As, simp_all)
  by (rule CompA_commute, simp_all)
    
thm Type_OK_def
thm Deterministic_def
thm internal_def
thm fb_out_less_step_def

thm mem_get_other_out
  
thm mem_get_comp_out
  

thm comp_out_in
  

lemma map_diff: "(\<And> b . b \<in> set x \<Longrightarrow> b \<noteq> a \<Longrightarrow> f b \<noteq> f a) \<Longrightarrow> map f x \<ominus> [f a] = map f (x \<ominus> [a])"
  by (induction x, simp_all)


lemma In_Equiv_fb_out_less_step_commute: "Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> x \<in> internal As \<Longrightarrow>  y \<in> internal As  \<Longrightarrow> x \<noteq> y \<Longrightarrow> loop_free As
  \<Longrightarrow> In_Equiv (fb_out_less_step x (fb_out_less_step y As)) (fb_out_less_step y (fb_out_less_step x As))"
proof -
  assume "Deterministic As"
  assume "x \<noteq> y"
  assume loopfree: "loop_free As"

  assume [simp]: "Type_OK As"
    
  from this have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> Out A = [out A]"
    using Type_OK_out by blast      
    
  define A where "A = get_comp_out x As"
  assume "x \<in> internal As"
  from this have A_As[simp]: "A \<in> set As" and out_A: "out A = x"
     by (simp_all add: A_def)

  define B where "B = get_comp_out y As"
  assume "y \<in> internal As"
  from this have B_As[simp]: "B \<in> set As" and out_B: "out B = y"
    by (simp_all add: B_def)
      
  have [simp]: " A \<noteq> B"
    using \<open>x \<noteq> y\<close> out_A out_B by auto
      
  from A_As obtain Bs Cs where As_A: "As = Bs @ A # Cs"
    by (meson split_list)

  from \<open>Type_OK As\<close> have "distinct As"
    using Type_OK_distinct by blast
  have As_minus_A: "As \<ominus> [A] = Bs @ Cs"
    apply (simp add: union_diff As_A)
    apply (subgoal_tac "Bs \<ominus> [A] = Bs")
     apply (subgoal_tac "Cs \<ominus> [A] = Cs")
      apply simp
     apply (metis AAA_c As_A  \<open>distinct As\<close> distinct.simps(2) distinct_append)
    by (metis AAA_c As_A UnCI \<open>distinct As\<close> append.simps(2) dist_perm distinct.simps(2) perm_tp set_append)
    
  have [simp]: "Out A = [out A]"
    using A_As Type_OK_out \<open>Type_OK As\<close> by blast
  have [simp]: "Out B = [out B]"
    using B_As Type_OK_out \<open>Type_OK As\<close> by blast
      
  from loopfree have "out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A)"
    apply (simp add: loop_free_def IO_Rel_def io_rel_def)
    apply (drule_tac x = "out A" in spec, safe)
    apply (subgoal_tac "(out A, out A) \<in> (UNION (set As) io_rel)\<^sup>+")
     apply simp
    apply (subst trancl_unfold_left)
    apply (simp add: relcomp_def OO_def)
    apply (rule_tac x = "out B" in exI, safe)
     apply (rule_tac x = A in bexI)
      apply (simp add: io_rel_def, simp_all)
      apply (rule r_into_rtrancl, simp)
    apply (rule_tac x = B in bexI)
     apply (simp add: io_rel_def)
    by simp
 
  have [simp]: "(fb_out_less_step x As) = map (CompA A) (As \<ominus> [A])"
    apply (simp add: fb_out_less_step_def A_def [THEN sym])
    apply (simp add: out_A[THEN sym])
    apply (subst mem_get_other_out, simp_all)
    by (simp add: fb_less_step_def)

  have [simp]: "(fb_out_less_step y As) =  map (CompA B) (As \<ominus> [B])"
    apply (simp add: fb_out_less_step_def B_def [THEN sym])
    apply (simp add: out_B[THEN sym])
    apply (subst mem_get_other_out, simp_all)
    by (simp add: fb_less_step_def As_A union_diff)
      
  thm mem_get_comp_out
    
  have y_out_CompA: "y = out (CompA A B)"
    by (metis A_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars.out_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> out_B)
      
  have x_out_CompA: "x = out (CompA B A)"
    by (metis B_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars.out_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> out_A)
    
  have [simp]: "Type_OK (map (CompA A) (As \<ominus> [A]))"
    by (metis A_As BaseOperationFeedbacklessVars.fb_out_less_step_def BaseOperationFeedbacklessVars.mem_get_other_out BaseOperationFeedbacklessVars_axioms Type_OK_fb_out_less_step_aux \<open>A \<equiv> get_comp_out x As\<close> \<open>Type_OK As\<close> \<open>fb_out_less_step x As = map (CompA A) (As \<ominus> [A])\<close> out_A)
    
  have [simp]: "Type_OK (map (CompA B) (As \<ominus> [B]))"
      by (metis B_As B_def BaseOperationFeedbacklessVars.fb_out_less_step_def BaseOperationFeedbacklessVars.mem_get_other_out BaseOperationFeedbacklessVars_axioms Type_OK_fb_out_less_step_aux \<open>Type_OK As\<close> \<open>fb_out_less_step y As = map (CompA B) (As \<ominus> [B])\<close> out_B)
    
      
  have [simp]: "get_comp_out y (map (CompA A) (As \<ominus> [A])) = CompA A B"
    apply (subgoal_tac "y = out (CompA A B)")
     apply (simp)
     apply (rule mem_get_comp_out)
      apply (simp_all add: set_diff image_def)
     apply (rule_tac x = B in bexI, simp_all)
    using \<open>A \<noteq> B\<close> apply blast
      using \<open>y = out (CompA A B)\<close> by blast
      
  have [simp]: "get_comp_out x (map (CompA B) (As \<ominus> [B])) = CompA B A"
    apply (subgoal_tac "x = out (CompA B A)")
     apply (simp)
     apply (rule mem_get_comp_out)
      apply (simp_all add: set_diff image_def)
     apply (rule_tac x = A in bexI, simp_all)
      by (rule x_out_CompA)
      
    thm mem_get_other_out
      
    have [simp]: "map (CompA A) (As \<ominus> [A]) \<ominus> [CompA A B] = map (CompA A) (As \<ominus> [A] \<ominus> [B])"
      apply (rule map_diff)
        by (metis A_As B_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms DiffE Type_OK_out \<open>Type_OK As\<close> list.simps(1) mem_get_comp_out set_diff)
      have [simp]: "map (CompA B) (As \<ominus> [B]) \<ominus> [CompA B A] = map (CompA B) (As \<ominus> [A] \<ominus> [B])"
        apply (subst map_diff)
         apply (metis A_As B_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms DiffE Type_OK_out \<open>Type_OK As\<close> list.simps(1) mem_get_comp_out set_diff)
          by (simp add: diff_sym)

  have [simp]: "fb_out_less_step y (map (CompA A) (As \<ominus> [A])) = map (CompA (CompA A B)) (map (CompA A) (As \<ominus> [A] \<ominus> [B]))"
    apply (simp add: fb_out_less_step_def fb_less_step_def y_out_CompA)
    apply (subst mem_get_other_out, simp_all)
     apply (simp add: image_def set_diff)
     apply (rule_tac x = B in bexI, simp_all)
    using \<open>A \<noteq> B\<close> apply blast
    by (simp add: y_out_CompA[THEN sym])
      
  have [simp]: "fb_out_less_step x (map (CompA B) (As \<ominus> [B])) = map (CompA (CompA B A)) (map (CompA B) (As \<ominus> [A] \<ominus> [B]))"
    apply (simp add: fb_out_less_step_def fb_less_step_def x_out_CompA)
    apply (subst mem_get_other_out, simp_all)
     apply (simp add: image_def set_diff)
     apply (rule_tac x = A in bexI, simp_all)
    by (simp add: x_out_CompA[THEN sym])
      thm In_Equiv_CompA_twice
  show ?thesis
    apply (simp del: map_map)
    apply (rule In_Equiv_CompA_twice)
            apply simp_all
          apply (simp add: set_diff, safe)
    using BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> apply blast
           apply (metis  \<open>A \<equiv> get_comp_out x As\<close> \<open>Type_OK As\<close> mem_get_comp_out out_A )
          apply (metis \<open>B \<equiv> get_comp_out y As\<close> \<open>Type_OK As\<close>  mem_get_comp_out out_B )
         apply (meson A_As BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close>)
    using B_As BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> apply blast
       apply (simp add: \<open>x \<noteq> y\<close> out_A out_B)
      using A_As Deterministic_def \<open>Deterministic As\<close> apply blast
      using B_As Deterministic_def \<open>Deterministic As\<close> apply blast
        using \<open>out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A)\<close> by blast
   
    qed
      
lemma [simp]: "Type_OK As \<Longrightarrow> In_Equiv As As"
proof (induction As)
  case Nil
  then show ?case
    by simp
next
  case (Cons a As)
  then show ?case
    apply simp
    by (simp add: Type_OK_def in_equiv_eq)
qed
  
lemma fb_less_append: "\<And> As . fb_less (x @ y) As = fb_less y (fb_less x As)"
  proof (induction x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a x)
    then show ?case 
      by simp
  qed
    
  thm in_equiv_tran

    
lemma In_Equiv_trans: "\<And> Bs Cs . Type_OK Cs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> In_Equiv Bs Cs \<Longrightarrow> In_Equiv As Cs"
  proof (induction As)
    case Nil
    show ?case
      apply (case_tac Bs)
      using Nil.prems(3) apply blast
      using Nil.prems(2) by auto
  next
    case (Cons a As)
    show ?case
      apply (case_tac Bs)
      using Cons.prems(2) apply auto[1]
      apply (case_tac Cs, simp_all)
      using Cons.prems(3) In_Equiv.simps(3) apply blast
      apply safe
       apply (rule_tac B = aaa in in_equiv_tran)
      using Cons.prems(1) Type_OK_cons apply blast
        apply (metis Cons.prems(1) Cons.prems(2) Cons.prems(3) In_Equiv.simps(2) Type_OK_cons in_equiv_tran)
      using Cons.prems(1) Type_OK_cons in_equiv_eq apply blast
      using Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(3) In_Equiv.simps(2) Type_OK_cons by blast
    qed
      

  
lemma In_Equiv_exists: "\<And> Bs . In_Equiv As Bs \<Longrightarrow> A \<in> set As \<Longrightarrow> \<exists> B \<in> set Bs . in_equiv A B"
  proof (induction As)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a As)
    then show ?case
      by (case_tac Bs, simp_all, safe, simp)
  qed
       
lemma In_Equiv_Type_OK: "\<And>Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> Type_OK As"
proof (induction As)
  case Nil
  show ?case
    apply (case_tac Bs)
    using Nil.prems(1) apply blast
    using In_Equiv.simps(4) Nil.prems(2) by blast
next
  case (Cons a As)
  from Cons(3) obtain b Cs where [simp]: "Bs = b # Cs" and A: "in_equiv a b" and B[simp]: "In_Equiv As Cs"
    using In_Equiv.elims(2) by blast
      
  from A have [simp]: "length (Out a) = 1"
    apply (simp add: in_equiv_def)
    by (metis Cons.prems(1) One_nat_def Type_OK_cons \<open>Bs = b # Cs\<close>)
      
  from A have C: "Out a = Out b"
    by (simp add: in_equiv_def)
      
  show ?case
    apply (subst Type_OK_cons, safe)
    using Cons.prems(1) Type_OK_cons \<open>Bs = b # Cs\<close> \<open>in_equiv a b\<close> in_equiv_io_diagram apply blast
      apply simp
     apply (cut_tac A = aa and As = As and Bs = Cs in  In_Equiv_exists, simp_all)
     apply safe
     apply (simp add: C in_equiv_def)
    using Cons(2)
     apply (simp add: Type_OK_def)
      apply auto [1]
    using B Cons.IH Cons.prems(1) Type_OK_cons \<open>Bs = b # Cs\<close> by blast
qed
  
      
lemma In_Equiv_internal_aux: "Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> internal As \<subseteq> internal Bs"
  apply (simp add: internal_def, safe)
  apply (frule_tac A = A in In_Equiv_exists, blast)   
  apply (frule_tac A = B in In_Equiv_exists, blast)
  apply safe
  apply (rule_tac x = Ba in bexI, safe)
   apply (simp add: in_equiv_def out_def)
    using In_Equiv_exists in_equiv_def perm_set_eq by blast
    
    
lemma In_Equiv_sym: "\<And> Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> In_Equiv Bs As"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all)
next
  case (Cons a As)
  then show ?case
    apply (case_tac Bs, simp_all)
    apply (rule in_equiv_sym, simp_all)
    using Type_OK_cons by blast
qed

lemma In_Equiv_internal: "Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> internal As = internal Bs"
  apply (frule In_Equiv_Type_OK, blast)
  apply (frule In_Equiv_internal_aux, blast)
  apply (drule_tac As = Bs and Bs = As in In_Equiv_internal_aux)
  by (rule In_Equiv_sym, simp_all)

lemma in_equiv_CompA: "in_equiv A A' \<Longrightarrow> in_equiv B B' \<Longrightarrow> io_diagram A' \<Longrightarrow> io_diagram B' \<Longrightarrow> in_equiv (CompA A B) (CompA A' B')"
  apply (simp add: CompA_def)
    apply (case_tac "out A \<in> set (In B)", simp_all, safe)
    apply (rule in_equiv_Comp, simp_all)
    apply (subst (asm) in_equiv_def) 
   apply (subst (asm) in_equiv_def, safe)
   apply (simp add: out_def)
  using perm_set_eq apply blast
    apply (subst (asm) in_equiv_def) 
   apply (subst (asm) in_equiv_def, safe)
   apply (simp add: out_def)
  using perm_set_eq by blast
    
lemma In_Equiv_fb_less_step_cong: "\<And> Bs . Type_OK Bs \<Longrightarrow> in_equiv A B \<Longrightarrow> io_diagram B \<Longrightarrow> In_Equiv As Bs
    \<Longrightarrow> In_Equiv (fb_less_step A As) (fb_less_step B Bs)"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all add: fb_less_step_def)
next
  case (Cons b As)
  then show ?case
    apply (case_tac Bs, simp_all)
    apply (simp add: fb_less_step_def)
    apply (rule in_equiv_CompA)
       apply simp_all
    using Type_OK_cons by blast
qed
  
lemma In_Equiv_append: "\<And> As' . In_Equiv As As' \<Longrightarrow> In_Equiv Bs Bs' \<Longrightarrow> In_Equiv (As @ Bs) (As' @ Bs')"   
proof (induction As)
  case Nil
  then show ?case
    apply (case_tac As')
    by simp_all
next
  case (Cons a As)
  then show ?case
    by (case_tac As', simp_all)
qed
  
lemma In_Equiv_split: "\<And> Bs . In_Equiv As Bs \<Longrightarrow> A \<in> set As 
    \<Longrightarrow> \<exists> B As' As'' Bs' Bs'' . As = As' @ A # As'' \<and> Bs = Bs' @ B # Bs'' \<and> in_equiv A B \<and> In_Equiv As' Bs' \<and> In_Equiv As'' Bs''"
proof (induction As)
  case Nil
  then show ?case
    by simp
next
  case (Cons a As)
  then show ?case
  proof (cases "a = A")
    case True
    from this and Cons show ?thesis
    apply (simp_all, safe)
      apply (case_tac Bs, simp_all)
     apply (rule_tac x = aa in exI)
     apply (rule_tac x = "[]" in exI)
      apply (rule_tac x = As in exI, simp)
     apply (rule_tac x = "[]" in exI)
     by (rule_tac x = list in exI, simp)      
  next
    case False
    obtain b Ba where [simp]: "Bs = b # Ba"
      using Cons.prems(1) In_Equiv.elims(2) by blast
    
    have "A \<in> set As"
      using Cons.prems(2) False by auto
        
    have "In_Equiv As Ba"
      using Cons.prems(1) \<open>Bs = b # Ba\<close> by auto
        
    have [simp]: "in_equiv a b"
      using Cons.prems(1) In_Equiv.simps(2) \<open>Bs = b # Ba\<close> by blast
        
    obtain B As' As'' Bs' Bs'' where [simp]: "As = As' @ A # As''" and [simp]: "Ba = Bs' @ B # Bs''" 
        and [simp]: "in_equiv A B" and [simp]: "In_Equiv As' Bs'" and [simp]: "In_Equiv As'' Bs''"
      using Cons.IH \<open>A \<in> set As\<close> \<open>In_Equiv As Ba\<close> by blast
        
    show ?thesis
      apply simp
      apply (rule_tac x = B in exI, simp)
      apply (rule_tac x = "a # As'" in exI, simp)
      by (rule_tac x = "b # Bs'" in exI, simp)
  qed  
qed

    
lemma In_Equiv_fb_out_less_step_cong: 
  assumes [simp]: "Type_OK Bs"
    and "In_Equiv As Bs"
    and internal: "a \<in> internal As"
    shows "In_Equiv (fb_out_less_step a As) (fb_out_less_step a Bs)"
proof -
  have [simp]: "Type_OK As"
    using In_Equiv_Type_OK assms(1) assms(2) by blast

  obtain A where "A \<in> set As" and "out A = a"
    using internal by (subst (asm) internal_Type_OK_simp, simp_all, blast)
      
  have [simp]: "get_comp_out a As = A"
    using \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_comp_out by blast
      
  have [simp]: "get_other_out a As = As \<ominus> [A]"
    using \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_other_out by blast
      
  obtain B As' As'' Bs' Bs'' where As_split: "As = As' @ A # As''" and Bs_split: "Bs = Bs' @ B # Bs''" and [simp]: "in_equiv A B" 
      and [simp]: "In_Equiv As' Bs'" and [simp]: "In_Equiv As'' Bs''"
    using In_Equiv_split \<open>A \<in> set As\<close> assms(2) by blast
      
  have "out B = a"
    by (metis \<open>in_equiv A B\<close> \<open>out A = a\<close> in_equiv_def out_def)
      
  have "B \<in> set Bs"
    by (simp add: \<open>Bs = Bs' @ B # Bs''\<close>)
      
  have [simp]: "get_comp_out a Bs = B"
    using \<open>B \<in> set Bs\<close> \<open>Type_OK Bs\<close> \<open>out B = a\<close> mem_get_comp_out by blast

  have [simp]: "get_other_out a Bs = Bs \<ominus> [B]"
    using \<open>B \<in> set Bs\<close> \<open>Type_OK Bs\<close> \<open>out B = a\<close> mem_get_other_out by blast
      
  have "distinct As"
    by (simp add: Type_OK_distinct )

  have [simp]: "As \<ominus> [A] = As' @ As''"
    apply (simp add: As_split union_diff)
    by (metis AAA_c As_split \<open>distinct As\<close> disjoint_insert(2) distinct.simps(2) distinct_append list.simps(15))
      
  have "distinct Bs"
    by (simp add: Type_OK_distinct)

  have Bs_diff: "Bs \<ominus> [B] = Bs' @ Bs''"
    apply (simp add: Bs_split union_diff)
    by (metis AAA_c Bs_split \<open>distinct Bs\<close> disjoint_insert(2) distinct.simps(2) distinct_append list.simps(15))
      

  show ?thesis
    apply (simp add: fb_out_less_step_def)
    apply (rule In_Equiv_fb_less_step_cong)
       apply (metis Diff_iff Type_OK_def \<open>get_other_out a Bs = Bs \<ominus> [B]\<close> assms(1) concat_map_Out_get_other_out distinct_diff set_diff)
      apply simp
    using Type_OK_def \<open>B \<in> set Bs\<close> assms(1) apply blast
    by (simp add: Bs_diff In_Equiv_append)
qed
 
lemma In_Equiv_IO_Rel: "\<And> Bs . In_Equiv As Bs \<Longrightarrow> IO_Rel Bs = IO_Rel As"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all)
next
  case (Cons a As)
    
  obtain B Bs' where [simp]: "Bs = B # Bs'"
    using In_Equiv.elims(2) local.Cons(2) by blast
  have [simp]: "(\<Union>x\<in>set Bs'. io_rel x) = (\<Union>x\<in>set As . io_rel x)"
    by (metis Cons.IH IO_Rel_def In_Equiv.simps(2) \<open>Bs = B # Bs'\<close> local.Cons(2) set_map)
      
  have "in_equiv a B"
    using Cons.prems by auto

  from this have [simp]: "io_rel a = io_rel B"
    by (metis in_equiv_def io_rel_def perm_set_eq)
     
  then show ?case
      by (simp add: IO_Rel_def)
qed
  
      
lemma In_Equiv_loop_free: "In_Equiv As Bs \<Longrightarrow> loop_free Bs \<Longrightarrow> loop_free As"
  apply (simp add: loop_free_def)
  by (subgoal_tac "IO_Rel Bs = IO_Rel As", simp_all add: In_Equiv_IO_Rel)
    
lemma loop_free_fb_out_less_step_internal: 
  assumes [simp]: "loop_free As"
    and [simp]: "Type_OK As"
    and "a \<in> internal As"
    shows "loop_free (fb_out_less_step a As)"
proof -
  obtain A where [simp]: "A \<in> set As" and [simp]: "out A = a"
    using assms(3) by (simp add: internal_Type_OK_simp, blast)
  show ?thesis
    by (rule_tac A = A in loop_free_fb_out_less_step, simp_all)
qed

lemma loop_free_fb_less_internal: 
  "\<And> As . loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x \<Longrightarrow> loop_free (fb_less x As)"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply (simp)
    apply (rule Cons(1))
       apply (rule loop_free_fb_out_less_step_internal)
         apply simp_all
    using Type_OK_fb_out_less_step_new apply blast
    by (metis Diff_empty internal_fb_out_less_step subset_Diff_insert)
qed

  
      
     
lemma In_Equiv_fb_less_cong: "\<And> As Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow>  distinct x \<Longrightarrow> loop_free Bs \<Longrightarrow> In_Equiv (fb_less x As) (fb_less x Bs)"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  have [simp]: "a \<in> internal Bs"
    by (metis Cons.prems(1) Cons.prems(2) Cons.prems(3) In_Equiv_internal list.set_intros(1) subsetCE)
  have [simp]: "Type_OK (fb_out_less_step a Bs)"
    using Cons.prems(1) Cons.prems(5) Type_OK_fb_out_less_step_new \<open>a \<in> internal Bs\<close> by blast
  have "Type_OK As"
    using Cons.prems(1) Cons.prems(2) In_Equiv_Type_OK by blast
  show ?case
    apply simp
    apply (rule Cons(1))
        apply simp_all
       apply (rule In_Equiv_fb_out_less_step_cong)
         apply (simp_all add: Cons)
    using Cons.prems(3) apply auto[1]
      apply (subst internal_fb_out_less_step)
    using Cons.prems(2) Cons.prems(5) In_Equiv_loop_free apply blast
        apply (simp add: \<open>Type_OK As\<close>)
    using Cons.prems(3) apply auto[1]
    using Cons.prems(3) Cons.prems(4) apply auto[1]
    using Cons.prems(4) apply auto [1]
    apply (rule loop_free_fb_out_less_step_internal)
    by (simp_all add: Cons)
qed
  
      
      
thm Type_OK_fb_out_less_step_new
  
lemma Type_OK_fb_less: "\<And> As . Type_OK As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK (fb_less x As)"
proof (induction x)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a x)
  then show ?case
    apply (simp)
    apply (rule Cons(1))
      apply (rule Type_OK_fb_out_less_step_new, simp_all)
      apply(subst internal_fb_out_less_step, simp_all)
     apply blast
    using loop_free_fb_out_less_step_internal by blast
qed
  
  
  
thm Deterministic_fb_out_less_step
  
thm internal_fb_out_less_step
  
lemma internal_fb_less: 
  "\<And> As . loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x \<Longrightarrow> internal (fb_less x As) = internal As - set x"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply simp
    apply (subst Cons(1))
        apply simp_all
    using loop_free_fb_out_less_step_internal apply blast
    using Type_OK_fb_out_less_step_new apply blast
     apply (metis Diff_empty internal_fb_out_less_step subset_Diff_insert)
    using internal_fb_out_less_step by auto    
qed
  

thm  Deterministic_fb_out_less_step
  
  
lemma Deterministic_fb_out_less_step_internal:
  assumes [simp]: "Type_OK As"
    and "Deterministic As"
    and internal: "a \<in> internal As"
  shows "Deterministic (fb_out_less_step a As)"
proof -
  obtain A where "A \<in> set As" and "out A = a"
    using internal by (simp add: internal_Type_OK_simp, blast)
  show ?thesis
    using Deterministic_fb_out_less_step \<open>A \<in> set As\<close> \<open>out A = a\<close> assms(1) assms(2) by blast
qed
  
lemma Deterministic_fb_less_internal: "\<And> As . Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x 
\<Longrightarrow> loop_free As \<Longrightarrow> Deterministic (fb_less x As)"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply simp
    apply (rule Cons(1), simp_all)
    using Type_OK_fb_out_less_step_new apply blast
    using Deterministic_fb_out_less_step_internal apply blast
      apply (subst internal_fb_out_less_step, simp_all, blast)
    using loop_free_fb_out_less_step_internal by blast
qed
  
    
lemma In_Equiv_fb_less_Cons: "\<And> As . Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> a \<in> internal As 
\<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow>  distinct (a # x)
  \<Longrightarrow> In_Equiv (fb_less (a # x) As) (fb_less (x @ [a]) As)"
proof (induction x)
  case Nil
  have [simp]:"Type_OK (fb_out_less_step a As)"
    using Nil.prems(1) Nil.prems(3) Nil.prems(4) Type_OK_fb_out_less_step_new by blast
  from Nil show ?case
    by simp_all
next
  case (Cons b x)
  have [simp]: "Type_OK (fb_out_less_step b As)"
    by (metis Cons.prems(1) Cons.prems(5) Type_OK_fb_out_less_step_new insert_subset list.simps(15))
  have [simp]: "Deterministic (fb_out_less_step b As)"
    apply (rule Deterministic_fb_out_less_step_internal)
      apply (simp_all add: Cons)
    using Cons.prems(5) by auto
  have [simp]: " Type_OK (fb_out_less_step a (fb_less x (fb_out_less_step b As)))"
    apply (rule Type_OK_fb_out_less_step_new, simp_all)
     apply (rule Type_OK_fb_less, simp_all)
       apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(5) Cons.prems(6) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)
    using Cons.prems(6) apply auto[1]
     apply (meson Cons.prems(1) Cons.prems(3) Cons.prems(5) list.set_intros(1) loop_free_fb_out_less_step_internal subset_iff)
    by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Diff_iff distinct.simps(2) fb_less.simps(2) internal_fb_less)
  have [simp]: "Type_OK (fb_out_less_step a (fb_out_less_step b As))"
    apply (rule Type_OK_fb_out_less_step_new, simp_all)
      by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) distinct_length_2_or_more insert_Diff insert_iff internal_fb_out_less_step list.set_intros(1) subset_eq)
  have [simp]: "set x \<subseteq> internal (fb_out_less_step b (fb_out_less_step a As))"
  proof -
    have f1: "\<And>v. v \<in> insert b (set x) \<or> set x \<subseteq> internal As - {v}"
      by (metis (no_types) Cons.prems(5) Diff_empty insert_subset list.simps(15) subset_Diff_insert)
    have "b \<in> internal As - {a}"
      by (metis (no_types) Cons.prems(5) Cons.prems(6) Diff_empty distinct.simps(2) insert_subset list.simps(15) subset_Diff_insert)
    then show ?thesis
      using f1 by (metis (no_types) Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(6) Diff_empty Type_OK_fb_out_less_step_new distinct.simps(2) internal_fb_out_less_step list.simps(15) loop_free_fb_out_less_step_internal subset_Diff_insert)
  qed
  have [simp]: "loop_free (fb_out_less_step a (fb_out_less_step b As))"
    by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Type_OK_fb_out_less_step_new distinct_length_2_or_more insert_Diff insert_iff insert_subset internal_fb_out_less_step list.simps(15) loop_free_fb_out_less_step_internal)
  have [simp]: "In_Equiv (fb_less x (fb_out_less_step a (fb_out_less_step b As))) (fb_out_less_step a (fb_less x (fb_out_less_step b As)))"
    apply (cut_tac Cons(1)[of "fb_out_less_step b As"])
          apply (simp add: fb_less_append)
         apply (simp_all add: Cons)
      
       apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(5) insert_subset list.simps(15) loop_free_fb_out_less_step_internal)
      apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) distinct_length_2_or_more insert_Diff insert_iff internal_fb_out_less_step list.set_intros(1) subsetCE)
     apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(5) Cons.prems(6) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)
    using Cons.prems(6) by auto      
  show ?case
    apply (simp add: fb_less_append)
    apply (rule_tac Bs = "(fb_less x (fb_out_less_step a (fb_out_less_step b As)))" in In_Equiv_trans)
      apply simp
      apply (rule In_Equiv_fb_less_cong)
         apply simp_all
        apply (rule In_Equiv_fb_out_less_step_commute)
             apply (simp_all add: Cons)
    using Cons.prems(5) apply auto[1]
    using Cons.prems(6) apply auto[1]
    using Cons.prems(6) by auto[1]
qed
 
    
theorem In_Equiv_fb_less: "\<And> y As . Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow>  distinct x \<Longrightarrow> perm x y
  \<Longrightarrow> In_Equiv (fb_less x As) (fb_less y As)"
  
proof (induction x)
  case Nil
  then show ?case
    by simp_all
next
  case (Cons a x)
  obtain y' y'' where A: "y = y' @ a # y''" and [simp]: "perm x (y' @ y'')"
    by (meson Cons.prems(6) split_perm)
      
  have [simp]: "Type_OK (fb_out_less_step a As)"
    by (meson Cons.prems(1) Cons.prems(4) Type_OK_fb_out_less_step_new list.set_intros(1) subset_eq)
      
  have [simp]: "Deterministic (fb_out_less_step a As)"
    by (metis Cons.prems(1) Cons.prems(2) Cons.prems(4) Deterministic_fb_out_less_step_internal insert_subset list.simps(15))
      
  have [simp]: "loop_free (fb_out_less_step a As)"
    by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) insert_subset list.simps(15) loop_free_fb_out_less_step_internal)
      
  have [simp]: "Type_OK (fb_out_less_step a (fb_less y' As))"
    apply (subgoal_tac "fb_out_less_step a (fb_less y' As) = fb_less (y' @ [a]) As")
     apply simp
     apply (rule Type_OK_fb_less, simp_all add: Cons)
      
    using Cons.prems(4) \<open>perm x (y' @ y'')\<close>
      apply (cut_tac perm_set_eq [of x "y' @ y''"], simp_all)
     apply (metis Cons.prems(5) UnI1 \<open>perm x (y' @ y'')\<close> dist_perm distinct.simps(2) distinct_append perm_set_eq set_append)
    by (simp add: fb_less_append)
      

  have [simp]: "Type_OK (fb_less y'' (fb_out_less_step a (fb_less y' As)))"
    apply (subgoal_tac "fb_less y'' (fb_out_less_step a (fb_less y' As)) = fb_less (y' @ a # y'') As")
      apply simp
     apply (rule Type_OK_fb_less, simp_all add: Cons)
      apply (metis (no_types, lifting) Cons.prems(4) ListProp.perm_set_eq \<open>x <~~> y' @ y''\<close> insert_subset le_sup_iff list.simps(15) set_append)
     apply (metis A Cons.prems(5) Cons.prems(6) \<open>perm x (y' @ y'')\<close> dist_perm distinct.simps(2) distinct_append not_distinct_conv_prefix)
    by (simp add: fb_less_append)
      
  have B: "distinct y \<and> set y \<subseteq> internal As"
    using Cons.prems(4) Cons.prems(5) Cons.prems(6) dist_perm perm_set_eq by blast
      
  have [simp]: "set y'' \<subseteq> internal (fb_less y' (fb_out_less_step a As))"
    apply (subst internal_fb_less, simp_all)
      apply (subst internal_fb_out_less_step, simp_all add: Cons)
    using Cons.prems(4) apply auto[1]
    using A B apply (simp add: subset_Diff_insert)
    using A Cons.prems(5) Cons.prems(6) dist_perm distinct_append apply blast
      apply (subst internal_fb_out_less_step, simp_all add: Cons)
    using Cons.prems(4) apply auto[1]
    using A B by auto
      
  have [simp]: "loop_free (fb_out_less_step a (fb_less y' As))"
  proof -
    have f1: "distinct y"
      using Cons.prems(5) Cons.prems(6) dist_perm by blast
    have "set y \<subseteq> internal As"
      using Cons.prems(4) Cons.prems(6) perm_set_eq by blast
    then have "loop_free (fb_less (y' @ [a]) As)"
      using f1 by (simp add: A Cons.prems(1) Cons.prems(3) loop_free_fb_less_internal)
    then show "loop_free (fb_out_less_step a (fb_less y' As))"
      by (simp add: fb_less_append)
  qed
      
  show ?case
    apply (simp add: A fb_less_append)
    apply (rule_tac Bs = "fb_less y'' (fb_less y' (fb_out_less_step a As))" in In_Equiv_trans, simp)
     apply (simp add: fb_less_append[THEN sym])
     apply (rule Cons(1), simp_all)
      apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)
    using Cons.prems(5) apply auto[1]
    apply (rule In_Equiv_fb_less_cong, simp_all)
      apply (cut_tac In_Equiv_fb_less_Cons, simp add: fb_less_append)
            apply (simp_all add: Cons)
    using Cons.prems(4) apply auto[1]
      using A B apply auto[1]
      apply (metis Cons.prems(5) UnI1 \<open>perm x (y' @ y'')\<close> dist_perm distinct.simps(2) distinct_append perm_set_eq set_append)
    by (metis A Cons.prems(5) Cons.prems(6) dist_perm distinct.simps(2) distinct_append)
qed
 
lemma [simp]: "in_equiv \<box> \<box>"
  apply (simp add: in_equiv_def)
  by (simp add: switch.simps(1))
    
  
lemma in_equiv_Parallel_list: "\<And> Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> in_equiv (Parallel_list As) (Parallel_list Bs)"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all)
next
  case (Cons a As)
    
  obtain B Bs' where A[simp]: "Bs = B # Bs'"
    using In_Equiv.elims(2) local.Cons(3) by blast
    
  have B: "in_equiv (Parallel_list As) (Parallel_list Bs')"
    apply (rule Cons(1))
    using Cons.prems by auto

  show ?case
    apply simp
    by (metis Cons.prems(1) Cons.prems(2) In_Equiv.simps(2) Type_OK_cons A
        B in_equiv_Parallel io_diagram_parallel_list)        
qed
  
  
thm FB_fb_less
  
lemma [simp]: "io_diagram A \<Longrightarrow> distinct (VarFB A)"
  by (simp add: VarFB_def)
    
lemma [simp]: "io_diagram A \<Longrightarrow> distinct (InFB A)"
  by (simp add: InFB_def)
    
theorem fb_perm_eq_Parallel_list:
  assumes [simp]: "Type_OK As"
    and [simp]: "Deterministic As"
    and [simp]: "loop_free As"
    shows "fb_perm_eq (Parallel_list As)"
proof (simp add: fb_perm_eq_def, safe)
  fix x
  assume perm [simp]: "perm x (VarFB (Parallel_list As))"
    
  have length: "length(VarFB (Parallel_list As)) = length x"
    by (metis Permutation.perm_length perm)

  define y where "y = VarFB (Parallel_list As)"
      
  define X where "X = Parallel_list (fb_less x As)"
  define Y where "Y = Parallel_list (fb_less y As)"

      
  have A: "(fb ^^ length x) ([x @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> x @ OutFB (Parallel_list As)]) 
      = [InFB (Parallel_list As) \<leadsto> In X] oo Trs X"
    and perm_x: "perm (InFB (Parallel_list As)) (In X)"
    apply (subst FB_fb_less, simp_all add: X_def perm_sym)
    by (subst FB_fb_less, simp_all add: X_def perm_sym)
      
  have B: "(fb ^^ length (VarFB (Parallel_list As))) ([VarFB (Parallel_list As) @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] 
      oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> VarFB (Parallel_list As) @ OutFB (Parallel_list As)]) 
      = [InFB (Parallel_list As) \<leadsto> In Y] oo Trs Y"
    and perm_y: "perm (InFB (Parallel_list As)) (In Y)"
    apply (subst FB_fb_less, simp_all add: Y_def y_def)
    by (subst FB_fb_less, simp_all add: Y_def y_def)
      
  thm In_Equiv_fb_less
    
  have [simp]: "set x \<subseteq> internal As"
    by (simp add: internal_VarFB)

  have perm[simp]: "perm (VarFB (Parallel_list As)) x"
    by (simp add: perm_sym)

  have "io_diagram (Parallel_list As)"
    using io_diagram_parallel_list assms(1) by blast
      
  from this have "distinct (VarFB (Parallel_list As))"
    by simp
      
  from this have [simp]: "distinct x"
    using perm dist_perm by blast
    

  have [simp]: "In_Equiv (fb_less x As) (fb_less y As)"
    by (rule In_Equiv_fb_less, simp_all add: y_def)
      
      
  have [simp]: "Type_OK (fb_less y As)"
    using Type_OK_fb_less \<open>distinct (VarFB (Parallel_list As))\<close> \<open>set x \<subseteq> internal As\<close> \<open>y \<equiv> VarFB (Parallel_list As)\<close> assms(1) assms(3) perm perm_set_eq by blast
      
  have [simp]: "io_diagram Y"
    by (simp add: Y_def io_diagram_parallel_list)
      
  have [simp]: "io_diagram (Parallel_list As)"
    by (simp add: io_diagram_parallel_list)

              
  have "in_equiv (Parallel_list (fb_less x As)) (Parallel_list (fb_less y As))"
    by (subst in_equiv_Parallel_list, simp_all)
     
      
  from this have "perm (In X) (In Y)" and "Trs X = [In X \<leadsto> In Y] oo Trs Y" and "Out X = Out Y"
    by (simp_all add: in_equiv_def X_def [THEN sym] Y_def [THEN sym])
          
      
  from this have "[InFB (Parallel_list As) \<leadsto> In X] oo Trs X = [InFB (Parallel_list As) \<leadsto> In X] oo ([In X \<leadsto> In Y] oo Trs Y)"
    by simp
  also have "... =  ([InFB (Parallel_list As) \<leadsto> In X] oo [In X \<leadsto> In Y]) oo Trs Y"
    by (simp add: comp_assoc)
  also have "... = [InFB (Parallel_list As) \<leadsto>  In Y] oo Trs Y"
    apply (subst switch_comp, simp_all add: perm_x)
    by (simp add: \<open>perm (In X) (In Y)\<close>)
  
  finally show  "(fb ^^ length (VarFB (Parallel_list As)))
          ([VarFB (Parallel_list As) @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] 
          oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> VarFB (Parallel_list As) @ OutFB (Parallel_list As)]) =
         (fb ^^ length (VarFB (Parallel_list As))) ([x @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] 
          oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> x @ OutFB (Parallel_list As)])"
    apply (simp add: B)
    by (simp add: length A)
qed
  
theorem FeedbackSerial_Feedbackless: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (In A) \<inter> set (In B) = {} (*required*)
      \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> fb_perm_eq (A ||| B) \<Longrightarrow> FB (A ||| B) = FB (FB (A) ;; FB (B))"
proof -
  assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"
          assume [simp]: "set (In A) \<inter> set (In B) = {}"
          assume [simp]: "set (Out A) \<inter> set (Out B) = {}"
            
          assume fb_perm_eq: "fb_perm_eq (A ||| B)"
            

          define I where "I \<equiv> (In (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B))"
            
          define O' where "O' \<equiv> (Out (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B))"

          define IA' where "IA' \<equiv> In A \<ominus> Out A \<ominus> Out B"
          define IB' where "IB' \<equiv> In B \<ominus> Out A \<ominus> Out B"

          define IA'' where "IA'' \<equiv> In A \<ominus> Out A"
          define IB'' where "IB'' \<equiv> In B \<ominus> Out B"

          define OA' where "OA' \<equiv> Out A \<ominus> In A \<ominus> In B"
          define OB' where "OB' \<equiv> Out B \<ominus> In A \<ominus> In B"
          
          define OA'' where "OA'' \<equiv> Out A \<ominus> In A"
          define OB'' where "OB'' \<equiv> Out B \<ominus> In B"

          have [simp]: "TI (Trs A) = TVs (In A)"
            apply (subgoal_tac "io_diagram A")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "TI (Trs B) = TVs (In B)"
            apply (subgoal_tac "io_diagram B")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "TO (Trs A) = TVs (Out A)"
            apply (subgoal_tac "io_diagram A")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "TO (Trs B) = TVs (Out B)"
            apply (subgoal_tac "io_diagram B")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have I_simp:"I = IA' @ IB'"
            apply (simp add: I_def IA'_def IB'_def Parallel_indep Var_def diff_filter inter_filter)
            apply (subgoal_tac "[a\<leftarrow>In A . (a \<in> set (Out A) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B)) \<and> (a \<in> set (Out B) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B))] = [x\<leftarrow>In A . x \<notin> set (Out A) \<and> x \<notin> set (Out B)]")
            apply simp
            apply (drule drop_assumption, simp)
            apply (rule filter_cong, auto)
            by (rule filter_cong, auto)

          have In_simp: "(In (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B)) = IA' @ IB'"
            apply (simp add: IA'_def IB'_def Parallel_indep Var_def diff_filter inter_filter)
            apply (subgoal_tac "[a\<leftarrow>In A . (a \<in> set (Out A) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B)) \<and> (a \<in> set (Out B) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B))] = [x\<leftarrow>In A . x \<notin> set (Out A) \<and> x \<notin> set (Out B)]")
            apply simp
            apply (drule drop_assumption, simp)
            apply (rule filter_cong, auto)
            by (rule filter_cong, auto)

          have O'_simp: "O' = OA' @ OB'"
            by (simp add: O'_def OA'_def OB'_def Parallel_indep Var_def diff_inter_left union_diff diff_union)
            
          have Out_simp: "(Out (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B)) = OA' @ OB'" 
            by (simp add: OA'_def OB'_def Parallel_indep Var_def diff_inter_left union_diff diff_union)

          have [simp]: "distinct O'"
            by (simp add: O'_def)

          have [simp]: "distinct I"
            by (simp add: I_def Parallel_indep Var_def)
          

          have [simp]: "distinct IA'"
            by (simp add: IA'_def)

          have [simp]: "distinct IB'"
            by (simp add: IB'_def)

          have [simp]: "TI (Trs (A ||| B)) = TVs (In (A ||| B))"
            by (simp add: Parallel_indep)

          have [simp]: "TO (Trs (A ||| B)) = TVs (Out (A ||| B))"
            by (simp add: Parallel_indep)
          
          have [simp]: "distinct (Out A)"
            apply (subgoal_tac "io_diagram A")
            apply (unfold io_diagram_def)[1]
            by simp_all
 
          have [simp]: "distinct (Out B)"
            apply (subgoal_tac "io_diagram B")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "distinct (Var A A)"
            by (simp add: Var_def )

          have [simp]: "distinct (Var B B)"
            by (simp add: Var_def )

          have [simp]: "distinct (Var A B)"
            by (simp add: Var_def )

          have [simp]: "distinct (Var B A)"
            by (simp add: Var_def )

          have setI: "set I  = set (In A) \<union> set (In B) - (set (Out A) \<union> set (Out B))"
            by (simp add: I_def Parallel_indep Var_def set_diff set_inter, auto)

          have [simp]: "set (Var A A) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast
          have [simp]: "set (Var A B) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast

          have [simp]: "set (Var B A) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast

          have [simp]: "set (Var B B) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast

          have [simp]: "set (Var A B) \<inter> set (Var B A) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var B B) \<inter> set (Var A B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: " set (Var B B) \<inter> set (Var B A) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var A A) \<inter> set (Var B B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var A A) \<inter> set (Var A B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var A A) \<inter> set (Var B A) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var A B) \<inter> set (Var B B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def Parallel_def set_diff)
            by blast

          have [simp]: "set (Var A B) \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def Parallel_def set_diff)
            by blast

          have [simp]: "set IA' \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def IA'_def Parallel_indep set_diff)
            by blast          

          have [simp]: "set IB' \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def IB'_def Parallel_indep set_diff)
            by blast 

          have [simp]: "distinct OA'"
            by (simp add: OA'_def )

          have [simp]: "distinct OB'" 
            by (simp add: OB'_def )

          have [simp]: "set (Var B A) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var B B) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: " set OA' \<inter> set (Var B B) = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set (Var B A) = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set OB' = {}"
            by (metis O'_simp \<open>distinct O'\<close> distinct_append)

          have [simp]: "set (Var A B) \<inter> set OA' = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A B) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A A) \<inter> set OA' = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A A) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var B B) \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B B) \<union> (set (Var B A) \<union> set OB')))"
            apply (simp add: OA'_def OB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B B) \<union> (set (Var B A) \<union> set OB')))"
            apply (simp add: OA'_def OB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set O' \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B B) \<union> (set (Var B A) \<union> set OB')))"
            apply (simp add: O'_def OA'_def OB'_def Parallel_indep Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var A B) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var B B) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set IA' \<inter> set (Var B B) = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set IA' \<inter> set (Var A B) = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set IA' \<inter> set IB' = {}"
            apply (simp add: IA'_def IB'_def set_diff)
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply blast
            by simp

          have [simp]: "set (Var B A) \<inter> set IA' = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var B A) \<inter> set (Var B B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var B A) \<inter> set (Var A B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var B A) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var A A) \<inter> set IA' = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast
          have [simp]: "set (Var A A) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (In A) \<subseteq> set (Var A A) \<union> (set (Var B A) \<union> set IA')"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> set IB')"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var A A) \<subseteq> set (Out A)"
            by (simp add: Var_def set_inter)

          have [simp]: "set (Var A B) \<subseteq> set (Out A)"
            by (simp add: Var_def set_inter)

          have [simp]: "set OA' \<subseteq> set (Out A)"
            apply (simp add: OA'_def set_diff)
            by blast

          have [simp]: "set (Var B B) \<subseteq> set (Out B)"
            by (simp add: Var_def set_inter)

          have [simp]: "set (Var B A) \<subseteq> set (Out B)"
            by (simp add: Var_def set_inter)

          have [simp]: "set OB' \<subseteq> set (Out B)"
            apply (simp add: OB'_def set_diff)
            by blast

          have [simp]: "set OB' \<inter> set (Var A A) = {}"
            apply (simp add: OB'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set OB' \<inter> set (Var A B) = {}"
            apply (simp add: OB'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set OB' \<inter> set OA' = {}"
            by (simp add: Int_commute)          

          have [simp]: "set (Var B A) \<inter> set (Var A A) = {} "
            by (simp add: Int_commute)          

          have [simp]: "set (Var B A) \<inter> set OA' = {}"
            by (simp add: Int_commute)          

          have [simp]: "set (Var B B) \<inter> set (Var A A) = {} "
            by (simp add: Int_commute)          

          have [simp]: "set (Var B B) \<inter> set OA' = {}"
            by (simp add: Int_commute)          

          have [simp]: "perm (Var B B @ Var A B @ Var B A @ I) (Var B A @ IA' @ Var B B @ Var A B @ IB')"
            by (simp add: I_simp perm_mset union_lcomm)

          have [simp]: "perm (Var B B @ Var B A @ OB' @ Var A B @ OA') (Var A B @ OA' @ Var B B @ Var B A @ OB')"
            by (simp add: perm_mset)

          have [simp]: "set IB' \<subseteq> set (Var A B) \<union> (set (Var B A) \<union> set I)"
            apply (simp add: I_simp)
            by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var A B) \<union> (set (Var B A) \<union> set I)"
            by blast

          have [simp]: "set IA' \<subseteq> set (Var A B) \<union> (set (Var B A) \<union> set I)"
            apply (simp add: I_simp)
            by blast

          have [simp]: "set IB' \<subseteq> set (Var B A) \<union> set I" 
            apply (simp add: I_simp)
            by blast

          have [simp]: "set IA' \<subseteq> set (Var B A) \<union> set I"
            apply (simp add: I_simp)
            by blast
          
          have [simp]: "set (Var A B) \<subseteq> set (Var B A) \<union> (set OB' \<union> (set (Var A B) \<union> set OA'))"
            by blast

          have [simp]: "set O' \<subseteq> set (Var B A) \<union> (set OB' \<union> (set (Var A B) \<union> set OA'))"
            apply (simp add: O'_simp)
            by safe

          have [simp]: "set IB' \<inter> set (Var B A) = {}"
            apply (simp add: IB'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set IB' \<inter> set IA' = {}"
            by (simp add: Int_commute)

          have [simp]: "set (Var A B) \<inter> set IA' = {}"
            by (simp add: Int_commute)

          have [simp]: "perm (Var B A @ I) (IB' @ Var B A @ IA')"
            by (simp add: I_simp perm_mset)

          have [simp]: "perm (Var A B @ OA' @ Var B A @ OB') (Var B A @ OB' @ Var A B @ OA')"
            by (metis append_assoc perm_tp)

          have [simp]: "set (Var B A) \<subseteq> set OA' \<union> (set (Var B A) \<union> set OB')"
            by blast

          have [simp]: "set O' \<subseteq> set OA' \<union> (set (Var B A) \<union> set OB')"
            apply (simp add: O'_simp)
            by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B A) \<union> set OB'))"
            by blast

          have [simp]: "set O' \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B A) \<union> set OB'))"
            apply (simp add: O'_simp)
            by blast

          have [simp]: "set (Var A B) \<inter> set O' = {}"
            by (simp add: O'_simp)

          have [simp]: "set OA' \<inter> set IB' = {}"
            apply (simp add: OA'_def IB'_def set_diff)
            by blast

          have [simp]: "set IA'' \<subseteq> set (Var B A) \<union> set IA'"
            apply (simp add: IA''_def IA'_def set_diff Var_def set_inter)
            by blast

          have [simp]: "perm (Var B A @ IA') IA''"
            proof -
              have A: "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) IA''"
                apply (simp add: IA''_def)
                  using perm_diff_left_inter perm_sym by blast
 
              have B: "((In A \<ominus> Out A) \<otimes> Out B) = (In A \<otimes> Out B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp

              have C: "perm (In A \<otimes> Out B) (Out B \<otimes> In A)"
                apply (simp add:  perm_mset)
                using \<open>distinct (Out B)\<close> \<open>io_diagram A\<close> perm_mset perm_switch_aux_d io_diagram_def
                  by metis

              have D: "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B))"
                by (simp add: B C perm_union_left)

              have E: "perm ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B)) (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B))"
                by (simp only: D perm_sym)

              show "perm (Var B A @ IA') IA''"
                apply (simp add: Var_def IA'_def)
                apply (subgoal_tac "perm ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B)) (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B))")
                 apply (subgoal_tac "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) IA''")
                  using perm_trans apply blast
                by (simp_all only: E A )
            qed

          have [simp]: "perm (Var A B @ OA') OA''"
            proof -
              have A: "perm (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''"
                apply (simp add: OA''_def)
                  using perm_diff_left_inter perm_sym by blast

              have B: "((Out A \<ominus> In A)) \<otimes> In B = (Out A \<otimes> In B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have C: "perm ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''"
                apply (subgoal_tac "perm (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''")
                apply (subgoal_tac "((Out A \<ominus> In A)) \<otimes> In B = (Out A \<otimes> In B)")
                apply auto
                apply (simp only: B)
                by (simp only: A)
              show "perm (Var A B @ OA') OA''"
                by (simp add: Var_def OA'_def C)
            qed           

          have [simp]: "perm (OA' @ Var A B) OA''"
            apply (subgoal_tac "perm (Var A B @ OA') OA''")
            apply (metis perm_mset perm_tp)
            by simp

          have [simp]: "perm (Out A) (Var A A @ OA'')"
            apply (simp add: OA''_def Var_def )
            using \<open>io_diagram A\<close> perm_switch_aux_c perm_sym io_diagram_def by blast

          have [simp]: "distinct OA''"
            by (simp add: OA''_def)

          have [simp]: "set (Var A A) \<inter> set OA'' = {}"
            apply (simp add: OA''_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A B) \<subseteq> set OA''"
            apply (simp add: OA''_def Var_def set_diff set_inter)
            by (simp add: Diff_Int_distrib2 inf.absorb_iff2 inf.left_commute)

         have [simp]: "set OA' \<subseteq> set OA''"
            apply (simp add: OA'_def OA''_def set_diff)
            by blast

         have [simp]: "perm (Var A B @ IB') IB''"
            proof -
              have A: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out B \<ominus> Out A)) IB''"
                apply (simp add: IB''_def)
                  using perm_diff_left_inter perm_sym by blast

              have B: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) IB''"
                apply (subst diff_sym)
                by (simp add: A)
 
              have C: "((In B \<ominus> Out B) \<otimes> Out A) = (In B \<otimes> Out A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp

              have D: "perm (In B \<otimes> Out A) (Out A \<otimes> In B)"
                apply (simp add: perm_mset)
                apply (subgoal_tac "distinct (Var A B)")
                apply (subgoal_tac "io_diagram B")
                apply (simp only: Var_def io_diagram_def)
                apply (metis Int_commute distinct_inter set_eq_iff_mset_eq_distinct set_inter)
                by simp_all

              have E: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B))"
                by (simp add: B C D perm_union_left)

              have F: "perm ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B)) (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B))"
                by (simp only: E perm_sym)

              show "perm (Var A B @ IB') IB''"
                apply (simp add: Var_def IB'_def)
                apply (subgoal_tac "perm ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B)) (((In B \<ominus> Out B) \<otimes> Out A) @(In B \<ominus> Out A \<ominus> Out B))")
                 apply (subgoal_tac "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) IB''")
                  using perm_trans apply blast
                by (simp_all only: F B)
            qed

         have [simp]: "perm (Out B) (Var B B @ OB'')"
           apply (simp add: OB''_def Var_def)
             by (metis diff_inter_left mset_inter_diff perm_mset union_code)

         have [simp]: "perm (OA'' @ IB') (Var A B @ OA' @ IB')"
            by (metis perm_union_left \<open>perm (Var A B @ OA') OA''\<close> append_assoc perm_sym)

         have [simp]: "perm (OA'' @ IB') (OA' @ Var A B @ IB')"
            by (metis perm_union_left \<open>perm (OA' @ Var A B) OA''\<close> append_assoc perm_sym)

         have [simp]: "perm (Var B A @ OB') OB''"
            proof -
              have A: "perm (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''"
                apply (simp add: OB''_def )
                  using perm_diff_left_inter perm_sym by blast
              have B: "(Out B \<ominus> In B) \<otimes> In A = (Out B \<otimes> In A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have C: "perm ((Out B \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''"
                apply (subgoal_tac "perm (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''")
                apply (subgoal_tac "(Out B \<ominus> In B) \<otimes> In A = (Out B \<otimes> In A)")
                apply (simp add: diff_filter inter_filter)
                apply (simp only: B)
                by (simp only: A)
              show "perm  (Var B A @ OB') OB''"
                apply (simp add: Var_def OB'_def)
                apply (subst diff_sym)
                by (simp add: C)
            qed 

         have [simp]: "perm (Out A @ Out B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B) @ (Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
            proof -
              have A: "perm (Out A) ((Out A \<otimes> In A) @ (Out A \<ominus> In A))"
                by (metis OA''_def Var_def \<open>perm (Out A) (Var A A @ OA'')\<close>)
              have B: "perm (Out A \<ominus> In A) (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                using perm_diff_left_inter by blast
              have C: "((Out A \<ominus> In A) \<otimes> In B) = (Out A \<otimes> In B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have D: "perm (Out A \<ominus> In A) ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out A \<ominus> In A) (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                 apply (subgoal_tac "((Out A \<ominus> In A) \<otimes> In B) = (Out A \<otimes> In B)")
                  apply simp
                apply (simp only: C)
                by (simp only: B)
              
              have E: "perm (Out A)  ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out A) ((Out A \<otimes> In A) @ (Out A \<ominus> In A))")
                 apply (subgoal_tac "perm (Out A \<ominus> In A) ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                  apply (metis perm_mset union_code)
                apply (simp only: D)
                by (simp only: A)

              have F: "perm (Out B) ((Out B \<otimes> In B) @ (Out B \<ominus> In B))"
                by (metis OB''_def Var_def \<open>perm (Out B) (Var B B @ OB'')\<close>)
              have G: "perm (Out B \<ominus> In B) (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                by (metis diff_sym perm_diff_left_inter)
              have H: "((Out B \<ominus> In B) \<otimes> In A) = (Out B \<otimes> In A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have I: "perm (Out B \<ominus> In B) ((Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out B \<ominus> In B) (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                 apply (subgoal_tac "((Out B \<ominus> In B) \<otimes> In A) = (Out B \<otimes> In A)")
                  apply simp
                apply (simp only: H)
                by (simp only: G)
              
              have J: "perm (Out B)  ((Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out B) ((Out B \<otimes> In B) @ (Out B \<ominus> In B))")
                 apply (subgoal_tac "perm (Out B \<ominus> In B) ((Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                  apply (metis perm_mset union_code)
                apply (simp only: I)
                by (simp only: F)
             
             show "perm (Out A @ Out B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B) @ (Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
              apply (subgoal_tac "perm (Out A)  ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                apply (subgoal_tac "perm (Out B)  ((Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                 apply (metis append.assoc perm_mset union_code)
              apply (simp only: J)
              by (simp only: E)
          qed

         have [simp]: "set IB'' \<subseteq> set (Var A B) \<union> set IB'"
            apply (simp add: IB''_def IB'_def set_diff Var_def set_inter)
            by blast

         have [simp]: "distinct OB''"
            by (simp add: OB''_def)

         have [simp]: "set (Var B B) \<inter> set OB'' = {}"
            apply (simp add: Var_def OB''_def set_inter set_diff)
            by blast

         have [simp]: "set (Var B A) \<subseteq> set OB''"
            apply (simp add: Var_def OB''_def set_inter set_diff)
            by (metis (no_types, hide_lams) Diff_Diff_Int Diff_Int_distrib Diff_eq_empty_iff Int_commute \<open>set (In A) \<inter> set (In B) = {}\<close> equalityI inf.cobounded2)
         
         have [simp]: "set OB' \<subseteq> set OB''"
            apply (simp add: OB'_def OB''_def)
            by (metis DiffE DiffI set_diff subsetI)


         have IA''_simp: "IA'' = (In A \<ominus> Var A A)"
            by (simp add: IA''_def Var_def diff_inter_right)

         have OA''_simp: "OA'' = (Out A \<ominus> Var A A)"
            by (simp add: OA''_def Var_def diff_inter_left)

         have IB''_simp: "IB'' = (In B \<ominus> Var B B)"
            by (simp add: IB''_def Var_def diff_inter_right)

         have OB''_simp: "OB'' = (Out B \<ominus> Var B B)"
            by (simp add: OB''_def Var_def diff_inter_left)

         have [simp]: "TI (Trs (FB A)) = TVs IA''"
            apply (simp add: FB_def Let_def IA''_simp)
            apply (cut_tac t="TVs (Var A A)" and ts="TVs(In A \<ominus> Var A A)" and ts'="TVs(Out A \<ominus> Var A A)" and
                S="([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])" in  TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            by (simp_all)

         have [simp]: "TO (Trs (FB A)) = TVs OA''"
            apply (simp add: FB_def Let_def OA''_simp)
            apply (cut_tac t="TVs (Var A A)" and ts="TVs(In A \<ominus> Var A A)" and ts'="TVs(Out A \<ominus> Var A A)" and
                S="([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])" in  TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            by simp_all

         have [simp]: "set OA'' \<inter> set IB' = {}"
            apply (simp add: OA''_def IB'_def set_diff)
            by blast

         have [simp]: "TI (Trs (FB B)) = TVs IB''"
            apply (simp add: FB_def Let_def IB''_simp)
            apply (cut_tac t="TVs (Var B B)" and ts="TVs(In B \<ominus> Var B B)" and ts'="TVs(Out B \<ominus> Var B B)" and
                S="([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])" in  TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            apply (simp)
            by (simp add: )

         have [simp]: "TO (Trs (FB B)) = TVs OB''"
            apply (simp add: FB_def Let_def OB''_simp)
            apply (cut_tac t="TVs (Var B B)" and ts="TVs(In B \<ominus> Var B B)" and ts'="TVs(Out B \<ominus> Var B B)" and
                S="([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])" in  TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            apply (simp)
            by (simp add: )

         have legth_Var_Parralel: "length (Var (A ||| B) (A ||| B)) = length (Var B A) + length (Var A B) + length (Var B B) + length (Var A A)"
            apply (simp add: Parallel_indep Var_def append_inter)
            apply (subgoal_tac "perm (Out A \<otimes> In A @ In B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B))")
            apply (simp add: perm_length)
            apply (subgoal_tac "perm (Out B \<otimes> In A @ In B) ((Out B \<otimes> In A) @ (Out B \<otimes> In B))")
            apply (simp add: perm_length)
            apply (simp add: inter_append)
            by (simp add: inter_append)

          have [simp]: "TI ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) = TVs (Var B A) @ TVs IA'"
            apply (cut_tac t="(TVs (Var A A))" and S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and ts="TVs(Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            by (simp_all)

          have [simp]: "TO ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) = TVs (Var A B) @ TVs OA'"
            apply (cut_tac t="(TVs (Var A A))" and S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and ts="TVs(Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var A A) = length (TVs (Var A A))")
              using TVs_append apply presburger
            by (simp add: TO_fb)

          have [simp]: "TI ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) = TVs (Var A B) @ TVs IB'"
            apply (cut_tac t="(TVs (Var B B))" and S="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" in TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var B B) = length (TVs (Var B B))")
              using TVs_append apply presburger
            by (simp add: TO_fb)
          
          have [simp]: "TO ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) = TVs (Var B A) @ TVs OB'"
            apply (cut_tac t="(TVs (Var B B))" and S="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" in TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var B B) = length (TVs (Var B B))")
              using TVs_append apply presburger
            by (simp add: TO_fb)

          have [simp]: "set OA' \<inter> set (Var A B) = {}"
            apply (simp add: OA'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set OB'' = {}"
            apply (simp add: OA'_def OB''_def set_diff)
            by (simp add: Diff_Int_distrib inf.commute)

          have In_FB_A_simp: "In (FB A) = IA''"
            by (simp add: FB_def Let_def Var_def IA''_def diff_inter_left diff_inter_right)

          have Out_FB_A_simp: "Out (FB A) = OA''"
            by (simp add: FB_def Let_def Var_def OA''_def diff_inter_left diff_inter_right)

          have In_FB_B_simp: "In (FB B) = IB''"
            by (simp add: FB_def Let_def Var_def IB''_def diff_inter_left diff_inter_right)

          have Out_FB_B_simp: "Out (FB B) = OB''"
            by (simp add: FB_def Let_def Var_def OB''_def diff_inter_left diff_inter_right)

          have [simp]: "(IB'' \<ominus> Var (FB A) (FB B)) = IB'"
            apply (simp add: FB_def Let_def Var_def IB''_def IB'_def diff_inter_right diff_inter_left)
            apply (subst diff_sym)
            apply (subst diff_notin)
            by (simp_all add: Int_commute)

          have [simp]:"(OA'' \<ominus> Var (FB A) (FB B)) = OA'"
            apply (simp add: FB_def Let_def Var_def OA''_def OA'_def diff_inter_right diff_inter_left)
            apply (subst diff_notin)
            apply (simp add: set_diff)
            apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
            apply blast
            by simp_all

          have[simp]: "set IA'' \<inter> set IB' = {}"
            apply (simp add: IA''_def IB'_def set_diff)
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply blast
            by simp

          have [simp]: "IA'' \<oplus> IB' = IA'' @ IB'"
            by (simp add: addvars_distinct)

          have [simp]: "distinct IA''"
            by (simp add: IA''_def)

          have [simp]: "Trs (FB A) \<parallel> ID (TVs IB') oo [OA''@ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) = Trs (FB (A) ;; FB (B))"
            apply (simp add: Comp_def Let_def In_FB_A_simp Out_FB_A_simp In_FB_B_simp Out_FB_B_simp)
            by (simp add: distinct_id)
         
          have In_FB_simp: "In (FB A ;; FB B) = IA'' @ IB'"
            by (simp add: Comp_def In_FB_A_simp Out_FB_A_simp In_FB_B_simp Out_FB_B_simp)

          have Out_FB_simp: "Out (FB A ;; FB B) = OA' @ OB''"
            by (simp add: Comp_def In_FB_A_simp Out_FB_A_simp In_FB_B_simp Out_FB_B_simp)

          have Var_FB_simp: "(Var (FB A ;; FB B) (FB A ;; FB B)) = Var B A"
            apply (simp add: Var_def In_FB_simp Out_FB_simp)
            apply (simp add: append_inter)
            apply (simp add: OA'_def OB''_def IA''_def IB'_def)
            apply (subgoal_tac "((Out A \<ominus> In A \<ominus> In B) \<otimes> (In A \<ominus> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) = []")
            apply simp
            apply (subgoal_tac "(Out B \<ominus> In B) \<otimes> (In A \<ominus> Out A) @ (In B \<ominus> Out A \<ominus> Out B) = (Out B \<ominus> In B) \<otimes> (In A \<ominus> Out A)")
            apply simp
            apply (subst inter_diff_distrib)
            apply (subgoal_tac "Out B \<otimes> (In A \<ominus> Out A) = (Out B \<otimes> In A)")
            apply simp
            apply (subgoal_tac "In B \<otimes> (In A \<ominus> Out A) =[]")
            apply (simp)
            apply (subgoal_tac "set (In B) \<inter> set(In A) = {}")
            apply (simp add: empty_inter_diff)
            apply (simp add: Int_commute)
            apply (subgoal_tac "set (Out B) \<inter> set (Out A) = {}")
            apply (subst inter_diff_empty)
            apply simp
            apply simp
            apply (simp add: Int_commute)
            apply (subst inter_addvars_empty)
            apply (simp add: set_diff)
            apply blast
            apply simp
            apply (subst empty_inter)
            apply (simp add: set_diff)
            apply blast
            by simp

          have [simp]: "(IA'' @ IB' \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = IA' @ IB'"
            apply (simp only: Var_FB_simp)
            apply (simp add: Var_def IA''_def IB'_def IA'_def)
            apply (simp add: union_diff)
            apply (subst diff_sym)
            apply (simp add: diff_inter_right)
            apply (subst diff_sym)
            apply (subst(5) diff_disjoint)
            apply (simp add: set_diff set_inter)
            apply blast
            by simp

          have [simp]: "(In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = IA' @ IB'"
            by (simp add: In_FB_simp)

          have [simp]: "(OA' @ OB'' \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = O'"
            apply (simp only: Var_FB_simp Out_FB_simp)
            apply (simp add: OA'_def OB''_def Var_def O'_simp OB'_def)
            apply (simp add: union_diff)
            apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
            apply (subst diff_inter_empty)
            apply (simp only: set_diff)
            apply blast
            apply (subst(2) diff_sym)
            apply (subst diff_inter_left)
            by simp_all

          have [simp]: "(Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = O'"
            by (simp add: Out_FB_simp)
   

          have aa: "perm ((((Var A A @ Var B B) @ Var A B) @ Var B A) @ I) (Var (A ||| B) (A ||| B) @ I)"
            apply (subgoal_tac "perm (((Var A A @ Var B B) @ Var A B) @ Var B A) (Var (A ||| B) (A ||| B))")
            apply (subst perm_union_left)
            apply simp_all
            apply (subgoal_tac "io_diagram A")
            apply (subgoal_tac "io_diagram B")
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply (simp add: perm_var_Par perm_sym)
            by simp_all

         
          have FB_Par_A_B: "FB (A ||| B) = 
            \<lparr>In = I, Out = O', Trs = (fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] 
            oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'])  \<rparr>"
            (is "_ = \<lparr>In=I,Out=O',Trs = ?T\<rparr>")

            by (simp add: FB_def Let_def I_def O'_def) 
              
          thm fb_perm_eq
          thm I_def
            
            have "[(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']
            = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo ([Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'] oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])"
              by (simp add: comp_assoc [THEN sym]) 
            also have "... = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']"
                  apply (subgoal_tac "[Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'] oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] = [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']")
                   apply simp
                  apply (subst switch_comp, simp_all)
                   apply (metis BaseOperationFeedbacklessVars.Parallel_def BaseOperationFeedbacklessVars.Var_def BaseOperationFeedbacklessVars_axioms O'_def mset_inter_diff perm_mset simps(2) union_code)
                  by (simp add: O'_def Var_def  set_addvars set_diff set_inter, auto)
                    
                also have "... = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']"
                  apply (subgoal_tac " [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)]")
                   apply simp
                  apply (subst switch_comp, simp_all)
                  using aa apply auto[1]
                  by (simp add: I_def Var_def  set_addvars set_diff set_inter)
                    
                    
                    
                    
                finally have ZZZ: "[(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] 
                oo ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] =
              [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] "
             by simp
                    
                    
                 
                
            
          from fb_perm_eq have fb_perm_eq_a: "\<And> x . perm x (VarFB (A ||| B)) \<Longrightarrow> (fb ^^ length (VarFB (A ||| B))) ([VarFB (A ||| B) @ InFB (A ||| B) \<leadsto> In A \<oplus> In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> VarFB (A ||| B) @ OutFB (A ||| B)]) =
        (fb ^^ length (VarFB (A ||| B))) ([x @ InFB (A ||| B) \<leadsto> In A \<oplus> In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> x @ OutFB (A ||| B)]) "
            by (simp add: fb_perm_eq_def )
             
          have "?T = (fb ^^ length (Var (A ||| B) (A ||| B))) (
              [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] )" (is "_ = ?Fb (?Sa oo (?Sb oo ?Tr oo ?Sc) oo ?Sd)")
            apply (subst ZZZ)
            apply (cut_tac fb_perm_eq_a[of "Var A A @ Var B B @ Var A B @ Var B A"])
             apply (simp add: O'_def I_def OutFB_def VarFB_def InFB_def)
              by (metis VarFB_def aa append_assoc perm_append2_eq)

          also have "... = ?Fb ((?Sa oo ?Sb) oo ?Tr oo (?Sc oo ?Sd))"
            apply (rule_tac f = "?Fb" in arg_cong)
            by (simp add: comp_assoc)
          also have "... = ?Fb ([(Var A A @ Var B B @ Var A B @ Var B A) @ I  \<leadsto> In (A ||| B)] oo ?Tr oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])"
            apply (subst switch_comp, simp_all)
            apply (unfold append_assoc [THEN sym])
            apply (simp only: aa)
            apply (simp add: Var_def Parallel_def set_addvars set_inter)
            apply auto [1]
            
              apply (simp add: setI)
              apply (simp add: setI)
              apply (simp add: perm_var_Par [THEN perm_sym])
            apply (subst switch_comp, simp_all add: Var_def set_inter setI Parallel_def O'_def)
              apply (metis (no_types, lifting) mset_inter_diff perm_mset union_code)
            by (auto simp add: set_addvars set_diff set_inter)
          also have "... = ?Fb ([Var A A @ Var B B @ Var A B @ Var B A @ I  \<leadsto> In A @ In B] oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O'])" (is "?Lhs = ?Fc ?SS")
            by (simp add: Parallel_indep)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               ([Var A A @ Var B B @ Var A B @ Var B A @ I  \<leadsto> In A @ In B] oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O']))))"
            apply (simp add: legth_Var_Parralel)
            by (simp add: funpow_add)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               (([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B]) 
               oo ?Tr oo [Out A @ Out B \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']))))"
            apply (subgoal_tac "[Var A A @ Var B B @ Var A B @ Var B A @ I \<leadsto> In A @ In B] = [Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B]")
            apply simp
            apply (subst par_switch)
            apply (simp_all)
            apply (subst switch_comp)
            apply (simp_all add: perm_union_right)
            by (simp add: Var_def set_inter IB'_def set_diff IA'_def, auto)
            
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               (([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B]) 
               oo ?Tr oo ([Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) )))) "
            apply (subgoal_tac "[Out A @ Out B \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] = [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']")
            apply simp
            apply (subst par_switch)
            apply (simp_all)
            apply (subst switch_comp)
            apply (simp_all)
            apply (simp add: Var_def OA'_def OB'_def)
            by (simp add: Var_def set_inter IB'_def set_diff IA'_def OB'_def OA'_def O'_def Parallel_def, auto)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B] 
               oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) ))) "
            apply (subst comp_assoc[THEN sym])
            apply (simp add:   Parallel_indep)
            using Parallel_indep TO_comp \<open>TI (Trs (A ||| B)) = TVs (In (A ||| B))\<close> \<open>TO (Trs (A ||| B)) = TVs (Out (A ||| B))\<close> apply auto[1]
            apply (subst comp_assoc)
              apply simp_all
              apply (simp add: addvars_def diff_distinct)
            apply (simp add: Parallel_indep)
            apply (subst comp_assoc)
            by (simp_all)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               (ID (TVs (Var A A)) \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B] 
               oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo ID (TVs (Var A A)) \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) ))) "
            apply (subst distinct_id)
            apply simp_all
            apply (subst distinct_id)
            by simp_all
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) (
              [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo
                ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B] 
                  oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'])) oo 
               [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) ))" (is "_ = ?Fc (?Sf oo _ oo ?Sh)")
            apply (cut_tac A= "[Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB']" and B = "[Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']" and tsa = "TVs (Var A A)"
              and S="([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'])" in fb_indep)
            apply (simp add: fbtype_def)
            apply safe
            by (simp_all add: Parallel_indep)
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB'  \<leadsto> In B]  oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'])) 
              oo ?Sh)"
            apply (subst par_switch)
            by simp_all 
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB'  \<leadsto> In B]  oo ?Tr oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']))
              oo ?Sh)"
            apply (subst(3) par_switch)
            by simp_all
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB'  \<leadsto> In B]  oo (Trs A \<parallel> Trs B) oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']))
              oo ?Sh)"
            by (simp add: Parallel_indep)
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])))
              oo ?Sh)"  
            by (simp add: comp_parallel_distrib)
          also have "... = ?Fc (?Sf oo 
                ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) \<parallel> ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])
              oo ?Sh)"
            apply (cut_tac S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and T="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" 
              and tsa= "TVs (Var A A)" and ts="TVs (Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in fb_gen_parallel)
            apply (simp add: fbtype_def )
            apply (subgoal_tac "length (Var A A)= length (TVs (Var A A))")
              apply presburger
            by simp
          also have "... = ?Fc (?Sf oo 
                ( [Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB']
                )
              oo ?Sh)"
            apply (cut_tac x="Var B A @ IA'" and y="Var B B @ Var A B @ IB'" and u="Var B B @ Var B A @ OB'" and v="Var A B @ OA'" and 
              S="((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']))" and 
              T="([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" in switch_par)
            by (simp_all)
          also have "... = ?Fc 
                ( (?Sf oo [Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA']) oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo ?Sh) )"
            by (simp add: comp_assoc_middle_ext)
          also have "... = ?Fc 
                ( [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo ?Sh) )"
            apply (subst switch_comp)
            apply (simp_all)
            by (auto simp add: IA'_def IB'_def)
          also have "... = ?Fc 
                ( [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O'] )"
            apply (subst switch_comp)
            by (simp_all)
          also have  "... = ?Fc 
                ( ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O'] )"
            apply (subst par_switch[THEN sym])
            apply simp_all
            apply (subst distinct_id)
            by simp_all
          also have  "... = ?Fc 
                ( ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  ID (TVs (Var B B)) \<parallel> [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'] )"
            apply (subst (2) par_switch[THEN sym])
            apply simp_all
            apply (subst distinct_id)
            by simp_all
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) 
                ( [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                    ((fb ^^ length (Var B B)) (([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])))) oo
                  [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))" 
            apply (cut_tac tsa="TVs (Var B B)" and A= "[Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA']" and B="[Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']" and
                S = "([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel>
                  (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" in fb_indep)
            by (simp_all add: fbtype_def)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) 
                ( [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                    ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))"  (is "_ = ?Fd (?Sk oo ?Sl \<parallel> ?Sm oo ?Sn) " )             
            apply (cut_tac tsa="TVs(Var B B)" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" and 
                S="([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" and
                T= "(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" in fb_gen_parallel)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            by (simp_all)
          also have "... = ?Fd (?Sk oo 
                ([Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo ?Sm \<parallel> ?Sl oo [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA']) oo 
                ?Sn)"
            apply (cut_tac x="Var A B @ IB'" and y="Var B A @ IA'" and u="Var A B @ OA'" and v="Var B A @ OB'" and
                T="(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" and
                S="(fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" in switch_par)
            by simp_all
          also have "... = ?Fd (
                (?Sk oo [Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB']) oo 
                  ?Sm \<parallel> ?Sl oo 
                ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo ?Sn))"
            by (simp add: comp_assoc_middle_ext)
          also have "... = ?Fd (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl oo 
                ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo ?Sn))"
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (auto simp add: IA'_def IB'_def)
          also have "... = ?Fd (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl oo 
                [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var A B @ Var B A @ O'])"
            apply (subst switch_comp)
            by simp_all

           also have "... = ?Fd (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl oo 
                ID (TVs (Var A B)) \<parallel> [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst(2) par_switch[THEN sym])
            apply simp_all
            by (simp add: distinct_id)


          also have "... = (fb ^^ length (Var B A)) (((fb ^^ length (Var A B)) (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl)) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (cut_tac tsa="TVs(Var A B)" and
                S="([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo
                  (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel>
                  (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']))" and 
                B="[OA' @ Var B A @ OB' \<leadsto> Var B A @ O']" in fb_indep_right)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A B)) = length (Var A B)")
            by (simp_all)
          also have "... = (fb ^^ length (Var B A))
                (?Sm \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (cut_tac u="Var A B" and x="Var B A @ IA'" and x'="IB'" and y="OA'" and y'="Var B A @ OB'" and
               A="(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" and
               B="(fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" in fb_par_serial)
            apply simp_all
            by (simp add: I_simp)
          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA'']) oo [Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (auto simp add: IA''_def Var_def set_inter set_diff)

          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo [Var A A @ IA'' \<leadsto> In A]) oo Trs A oo ([Out A \<leadsto> Var A A @ OA''] oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA'])) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst (3) switch_comp, simp_all)
            by (auto simp add: OA''_def OA'_def Var_def set_inter set_diff)

          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            by (simp add: comp_assoc [THEN sym])
          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst par_switch)
            by simp_all
          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A \<leadsto> Var A A] \<parallel> [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst(3) par_switch)
            by simp_all
          also have "... = (fb ^^ length (Var B A))
                (([Var B A @ IA' \<leadsto> IA''] oo (fb ^^ length (Var A A)) ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (cut_tac tsa="TVs ((Var A A))" and A="[Var B A @ IA' \<leadsto> IA'']" and B="[OA'' \<leadsto> Var A B @ OA']" and
                S="([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA''])" in fb_indep)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            apply (simp add: distinct_id)
            by (simp )
          also have "... = (fb ^^ length (Var B A))
                (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB(A)) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])" (is "_ = ?Fe (?So oo ID (TVs OA') \<parallel> ?Sl oo ?Sp)")
            apply (simp add: FB_def Let_def)
            apply (subgoal_tac "IA'' = (In A \<ominus> Var A A)")
            apply (subgoal_tac "OA'' = (Out A \<ominus> Var A A)")
            apply simp
            by (simp_all add: OA''_def IA''_def Var_def diff_inter_left diff_inter_right)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])
                oo ?Sp)"
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (auto simp add: Var_def IB'_def IB''_def set_inter set_diff)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo ([Out B \<leadsto> Var B B @ OB'' ] oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB']))
                oo ?Sp)"
            apply (subst(3) switch_comp)
            apply simp_all
            by (auto simp add: Var_def OB'_def OB''_def set_inter set_diff)

          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB'])
                oo ?Sp)"
            by (simp add: comp_assoc [THEN sym] )
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB'])
                oo ?Sp)"
            apply (subst par_switch)
            by simp_all
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo [Var B B \<leadsto> Var B B] \<parallel> [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)"
            apply (subst(3) par_switch)
            by simp_all
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo (fb ^^ length (Var B B)) ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo  [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)"
            apply (cut_tac tsa="TVs (Var B B)" and A="[Var A B @ IB' \<leadsto> IB'']" and B="[OB'' \<leadsto> Var B A @ OB']" and
                S="([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB''])"in fb_indep)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            by (simp_all add: distinct_id)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo  [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)" (is "_ = ?Fe (?Sq oo ?Sr oo ?St oo ?Sp)")
            apply (subst(3) FB_def)
            apply (simp add: Let_def)
            apply (subgoal_tac "IB'' = (In B \<ominus> Var B B)")
            apply (subgoal_tac "OB'' = (Out B \<ominus> Var B B)")
            by (simp_all add: OB''_def IB''_def Var_def diff_inter_left diff_inter_right)
          also have "... = ?Fe (
                ([Var B A @ IA' \<leadsto> IA''] \<parallel> ID (TVs IB') oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB')) oo 
                ?Sr oo ?St oo ?Sp)"
            by (simp add: distinct_id[THEN sym] par_id_comp)
          also have "... = ?Fe (
                ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB')) oo 
                ?Sr oo ?St oo ?Sp)"
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (
                ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA''@ IB' \<leadsto> Var A B @ OA'@ IB']) oo 
                ?Sr oo ?St oo ?Sp)" (is "_=?Fe (?Ss oo ?Sr oo ?St oo ?Sp)")
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (?Ss oo ?Sr oo
                (ID (TVs OA') \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo
                ?Sp)"
            by (simp add: distinct_id[THEN sym] id_par_comp)
          also have "... = ?Fe (?Ss oo ?Sr oo
                ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo
                ?Sp)"            
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (?Ss oo ?Sr oo
                ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo [OA' @ OB'' \<leadsto> OA' @ Var B A @ OB']) oo
                ?Sp)"  
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                ([OA''@ IB' \<leadsto> Var A B @ OA'@ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))"  
             by (simp add: comp_assoc  )
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                ([OA''@ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))"  
            apply (subst switch_comp, simp_all)
            by (auto simp add: OA'_def Var_def IB'_def)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                [OA''@ IB' \<leadsto> OA' @ IB''] oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))"  
            apply (subst switch_comp, simp_all)
            by (auto simp add: OA'_def Var_def IB''_def IB'_def set_diff set_inter)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                [OA''@ IB' \<leadsto> OA' @ IB''] oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                [OA' @ OB'' \<leadsto> Var B A @ O'])"  
            by (simp add: switch_comp perm_sym perm_union_right)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo 
                (Trs (FB (A) ;; FB (B))) oo
                [OA' @ OB'' \<leadsto> Var B A @ O'])"
             by (simp add: comp_assoc)
          also have Az: "... = Trs (FB (FB (A) ;; FB (B)))"
            apply (subst(3) FB_def)
            apply (simp add: Let_def In_FB_simp Out_FB_simp)
            by (simp add: Var_FB_simp)

          finally have A: "(fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'])
              =  Trs (FB (FB (A) ;; FB (B)))"
            by simp

       show "FB (A ||| B) = FB (FB (A) ;; FB (B))"
          proof -
            have "FB (A ||| B) = \<lparr>In = In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B), Out = Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B), Trs 
          = (fb ^^ length (Var (FB A ;; FB B) (FB A ;; FB B))) 
                ([Var (FB A ;; FB B) (FB A ;; FB B) @ (In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) \<leadsto> In (FB A ;; FB B)] oo Trs (FB A ;; FB B) 
              oo [Out (FB A ;; FB B) \<leadsto> Var (FB A ;; FB B) (FB A ;; FB B) @ (Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B))])\<rparr>"
              
              
              using A I_def In_FB_simp In_simp Out_FB_simp Var_FB_simp Az FB_Par_A_B 
               \<open>In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B) = IA' @ IB'\<close> 
               \<open>Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B) = O'\<close> by auto
              
            then show ?thesis
              by (metis FB_def)
          qed
        qed
          
declare io_diagram_distinct [simp del]  

          
    lemma in_out_equiv_FB_less: "io_diagram B \<Longrightarrow> in_out_equiv A B \<Longrightarrow> fb_perm_eq A \<Longrightarrow>  in_out_equiv (FB A) (FB B)"
      proof -
        assume A: "io_diagram B"
        assume B: "in_out_equiv A B"
          
        have [simp]: "perm (Var A A) (Var B B)"
          apply (simp add: Var_def)
          using B in_out_equiv_def perm_ops by blast
            
        from this have [simp]: "perm (Var B B) (Var A A)"
          by (rule perm_sym)

        have [simp]: "length (Var A A) = length (Var B B)"
          using [[simp_trace]]
          using A B apply (unfold io_diagram_def in_out_equiv_def)
          apply (simp add:  Var_def)
          apply (subgoal_tac "perm (Out A \<otimes> In A) (Out B \<otimes> In B)")
          using perm_length apply blast
          by simp
        have [simp]: "TI (Trs B) = TVs (In B)" and [simp]: "TO (Trs B) = TVs (Out B)" and [simp]: "distinct (In A)" and [simp]: "distinct (Out A)" 
          and [simp]: "distinct (Out B)" and [simp]: "perm (Out B) (Out A)"
          using A B apply (simp_all add: io_diagram_def in_out_equiv_def Var_def perm_sym)
          using dist_perm perm_sym apply blast
          using dist_perm perm_sym by blast
            
        have "perm (In A) (In B)"
          using B in_out_equiv_def by blast
         
        from this have [simp]: "set (In B) \<subseteq> set (In A)"
          by simp

        from B have X: "Trs A = [In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]"
          by (simp add: in_out_equiv_def)
            
        from this have Y: "\<And> x y . perm x (In A) \<Longrightarrow> perm y (Out A) \<Longrightarrow> [x \<leadsto> In A] oo Trs A oo [Out A \<leadsto> y]
            = [x \<leadsto> In B] oo Trs B oo [Out B \<leadsto> y]"
        proof -
          fix x y
          assume "perm x (In A)"
          assume "perm y (Out A)"
          have "[x \<leadsto> In A] oo Trs A oo [Out A \<leadsto> y] = [x \<leadsto> In A] oo ([In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]) oo [Out A \<leadsto> y]"
            by (simp add: X)
          also have "... = ([x \<leadsto> In A] oo [In A \<leadsto> In B]) oo Trs B oo ([Out B \<leadsto> Out A] oo [Out A \<leadsto> y])"
            by (simp add: comp_assoc)
          also have "... = [x \<leadsto> In B] oo Trs B oo [Out B \<leadsto> y]"
            by (metis \<open>distinct (In A)\<close> \<open>distinct (Out B)\<close> \<open>perm (Out B) (Out A)\<close> \<open>perm x (In A)\<close> \<open>perm y (Out A)\<close> \<open>set (In B) \<subseteq> set (In A)\<close> dist_perm order_refl perm_set_eq perm_sym switch_comp)
          finally show "[x \<leadsto> In A] oo Trs A oo [Out A \<leadsto> y] = [x \<leadsto> In B] oo Trs B oo [Out B \<leadsto> y]"
            by simp
        qed
          
        have [simp]: "perm (Var B B @ (In A \<ominus> Var A A)) (In A)"
          by (metis (no_types, lifting) Var_def \<open>distinct (In A)\<close> \<open>distinct (Out B)\<close> \<open>perm (In A) (In B)\<close> \<open>perm (Out B) (Out A)\<close> diff_inter_right list_inter_set perm_diff_eq perm_set_eq perm_switch_aux_f)
             
        have [simp]: "perm (Var B B @ (Out A \<ominus> Var A A)) (Out A)"
          by (metis Var_def \<open>distinct (In A)\<close> \<open>distinct (Out A)\<close> \<open>perm (Var B B) (Var A A)\<close> diff_inter_left perm_mset perm_switch_aux_c union_code)

        assume "fb_perm_eq A"
        from this have H: "(fb ^^ length (Var B B)) ([Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)]) =
              (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
          apply (simp add:fb_perm_eq_def InFB_def VarFB_def OutFB_def)
          apply (drule_tac x = "Var B B" in spec)
          by (simp add:  Y)
            
        have [simp]: "set (Var B B) \<inter> set (In A \<ominus> Var A A) = {}"
          by (metis Var_def \<open>distinct (In A)\<close> \<open>distinct (Out A)\<close> \<open>perm (Var A A) (Var B B)\<close> addvars_def distinct_addvars distinct_append distinct_inter perm_set_eq)
        have [simp]: "set (In B \<ominus> Var B B) \<subseteq> set (In A \<ominus> Var A A)"
          by (metis (full_types) B \<open>perm (Var A A) (Var B B)\<close> in_out_equiv_def order_refl perm_diff perm_set_eq)
        have [simp]: " perm (Var B B @ (In A \<ominus> Var A A)) (Var B B @ (In B \<ominus> Var B B))"
          using B \<open>perm (Var A A) (Var B B)\<close> in_out_equiv_def perm_diff perm_union_right by blast
        have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> set (In B \<ominus> Var B B)"
          by (simp add: set_diff)
          
        have [simp]: "set (Out A \<ominus> Var A A) \<subseteq> set (Out B \<ominus> Var B B)"
          by auto
        have [simp]: "perm (Out B) (Var B B @ (Out B \<ominus> Var B B))"
          by (metis A Var_def diff_inter_left perm_switch_aux_c perm_sym io_diagram_def)
        have [simp]: " set (Out A \<ominus> Var A A) \<subseteq> set (Var B B) \<union> set (Out B \<ominus> Var B B)"
          using \<open>set (Out A \<ominus> Var A A) \<subseteq> set (Out B \<ominus> Var B B)\<close> by blast
        have [simp]: "perm (Var A A @ (In A \<ominus> Var A A)) (Var B B @ (In A \<ominus> Var A A))"
          using \<open>perm (Var A A) (Var B B)\<close> perm_union_left by blast
        have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> set (In A \<ominus> Var A A)"
          using \<open>set (In B \<ominus> Var B B) \<subseteq> set (In A \<ominus> Var A A)\<close> \<open>set (In B) \<subseteq> set (Var B B) \<union> set (In B \<ominus> Var B B)\<close> by blast
        have [simp]: "perm (Out B) (Var B B @ (Out A \<ominus> Var A A))"
          by (meson \<open>perm (Out B) (Out A)\<close> \<open>perm (Out B) (Var B B @ (Out B \<ominus> Var B B))\<close> \<open>perm (Var A A) (Var B B)\<close> perm_diff perm_sym perm_trans perm_union_right)
        have [simp]: "set (Var A A) \<subseteq> set (Var B B) \<union> set (Out A \<ominus> Var A A)"
          using ListProp.perm_set_eq \<open>Var A A <~~> Var B B\<close> by blast

        have C: "ID (TVs (Var B B)) \<parallel> [In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo [Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] =  [Var B B @ (In A \<ominus> Var A A) \<leadsto> In B]"
          
          apply (subst distinct_id [THEN sym])
            apply (simp_all add: par_switch switch_comp)
          apply (subst switch_comp, simp_all)
            using \<open>In A <~~> In B\<close> by auto
              
        have D: "[Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)] oo ID (TVs (Var B B)) \<parallel> [Out B \<ominus> Var B B \<leadsto> Out A \<ominus> Var A A] = [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)]"
          by (subst distinct_id [THEN sym], simp_all add: par_switch switch_comp)
        have E: "[Var A A @ (In A \<ominus> Var A A) \<leadsto> Var B B @ (In A \<ominus> Var A A)] oo [Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] = [Var A A @ (In A \<ominus> Var A A) \<leadsto> In B]"
          by (subst switch_comp, simp_all)
        have F: "[Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)] oo [Var B B @ (Out A \<ominus> Var A A) \<leadsto> Var A A @ (Out A \<ominus> Var A A)] =  [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)]"
          by (subst switch_comp, simp_all)
        have "[In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo (fb ^^ length (Var B B)) ([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo (Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])) oo [Out B \<ominus> Var B B \<leadsto> Out A \<ominus> Var A A]
          = (fb ^^ length (Var B B))
            ((ID (TVs (Var B B)) \<parallel> [In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo [Var B B @ (In B \<ominus> Var B B) \<leadsto> In B]) oo Trs B 
            oo ([Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)] oo ID (TVs (Var B B)) \<parallel> [Out B \<ominus> Var B B \<leadsto> Out A \<ominus> Var A A]))"
          apply (subst fb_indep_a [THEN sym])
            apply (simp_all add: fbtype_def)
            apply (simp add: )
          by (simp add: comp_assoc)
        also have "... = (fb ^^ length (Var B B)) ([Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)])"
        by (simp add: C D)
      
      also have "... = (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
        by (simp add: H)
      also from B have "... = (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo ([In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]) oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
          apply (simp add: comp_assoc [THEN sym] switch_comp in_out_equiv_def)
          by (simp add: comp_assoc switch_comp)

      finally show ?thesis
        using A B apply (simp add: FB_def in_out_equiv_def Let_def)
        by (simp add: comp_assoc [THEN sym] switch_comp)
      qed
end
  
end