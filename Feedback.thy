theory Feedback imports AlgebraFeedback FeedbacklessPerm
begin
context BaseOperationVars
begin
thm fb_perm
  
lemma [simp]: "io_diagram A \<Longrightarrow> distinct (OutFB A)"
  by (simp add: OutFB_def io_diagram_distinct(2))
  
lemma io_diagram_fb_perm_eq: "io_diagram A \<Longrightarrow> fb_perm_eq A"
proof (simp add: fb_perm_eq_def, safe)
  fix x
  assume [simp]: "perm x (VarFB A)"
  assume [simp]: "io_diagram A"
    
  have [simp]: "perm (VarFB A) x"
    by (simp add: perm_sym)
      
  have [simp]: "set (VarFB A) \<inter> set (InFB A) = {}"
    by (simp add: VarFB_def Var_def InFB_def)
      
      
  have [simp]: "set (VarFB A) \<inter> set (OutFB A) = {}"
    by (simp add: VarFB_def Var_def OutFB_def)
      
  have [simp]: "perm (Out A) (VarFB A @ OutFB A)"
    by (metis OutFB_def VarFB_def Var_def \<open>io_diagram A\<close> diff_inter_left perm_switch_aux_c perm_sym io_diagram_def)
      
  have [simp]: "set x \<subseteq> set (VarFB A) \<union> set (OutFB A)"
    using \<open>perm x (VarFB A)\<close> perm_set_eq by blast
      
  have [simp]: "distinct x"
    using \<open>perm x (VarFB A)\<close> 
    by (metis VarFB_def Var_def \<open>perm (VarFB A) x\<close> \<open>io_diagram A\<close> dist_perm distinct_inter io_diagram_def)
  have "set x \<inter> set (InFB A) = {}"
    using \<open>perm x (VarFB A)\<close>
    by (metis Diff_disjoint InFB_def perm_diff_eq set_diff)
      
  have [simp]: "set (In A) \<subseteq> set (VarFB A) \<union> set (InFB A)"
    by (simp add: InFB_def set_diff)
      
  have [simp]: "set x \<inter> set (InFB A) = {}"
    by (simp add: \<open>set x \<inter> set (InFB A) = {}\<close>)
      
  have [simp]: "TI (Trs A) = TVs (In A)"
    using \<open>io_diagram A\<close> io_diagram_distinct(3) by blast
  have [simp]: "TO (Trs A) = TVs (Out A)"
    using \<open>io_diagram A\<close> io_diagram_distinct(4) by blast
  have [simp]: "distinct (Out A)"
    using \<open>io_diagram A\<close> io_diagram_distinct(2) by blast
    
  have "(fb ^^ length (VarFB A)) ([VarFB A @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> VarFB A @ OutFB A]) 
    = (fb ^^ length (VarFB A)) ([x @ InFB A \<leadsto> VarFB A @ InFB A] 
      oo ([VarFB A @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> VarFB A @ OutFB A]) 
      oo [VarFB A @ OutFB A \<leadsto> x @ OutFB A])"
    
    by (subst fb_perm, simp_all add: fbtype_def)
  also have "... = (fb ^^ length (VarFB A)) ( ([x @ InFB A \<leadsto> VarFB A @ InFB A] 
      oo [VarFB A @ InFB A \<leadsto> In A]) oo Trs A oo ([Out A \<leadsto> VarFB A @ OutFB A]
      oo [VarFB A @ OutFB A \<leadsto> x @ OutFB A]))"
    by (simp add: comp_assoc)
  also have "... = (fb ^^ length (VarFB A)) ( ([x @ InFB A \<leadsto> In A]) oo Trs A oo ([Out A \<leadsto> x @ OutFB A]))"
    apply (subgoal_tac "[x @ InFB A \<leadsto> VarFB A @ InFB A] oo [VarFB A @ InFB A \<leadsto> In A] = [x @ InFB A \<leadsto> In A]")
     apply simp
     apply (subgoal_tac "[Out A \<leadsto> VarFB A @ OutFB A] oo [VarFB A @ OutFB A \<leadsto> x @ OutFB A] = [Out A \<leadsto> x @ OutFB A]")
      apply simp
     by (simp_all add:  switch_comp)
      
    
  finally show "(fb ^^ length (VarFB A)) ([VarFB A @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> VarFB A @ OutFB A]) =
         (fb ^^ length (VarFB A)) ([x @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> x @ OutFB A])"
    by simp
qed
  
theorem FeedbackSerial: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (In A) \<inter> set (In B) = {} (*required*)
  \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> FB (A ||| B) = FB (FB (A) ;; FB (B))"
  
  apply (rule FeedbackSerial_Feedbackless, simp_all)
  apply (rule io_diagram_fb_perm_eq)
  by (simp add: io_diagram_Parallel)
  
lemmas fb_perm_sym = fb_perm [THEN sym]
  
declare length_TVs [simp del]

declare [[simp_trace_depth_limit=40]]
  

lemma in_out_equiv_FB: "io_diagram B \<Longrightarrow> in_out_equiv A B \<Longrightarrow> in_out_equiv (FB A) (FB B)"
  apply (rule in_out_equiv_FB_less, simp_all)
  apply (rule io_diagram_fb_perm_eq)
  using in_out_equiv_io_diagram by blast

end
 
end