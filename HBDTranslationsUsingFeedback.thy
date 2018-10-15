section{*HBD Translation Algorithms that use Feedback Composition*}

(* Was: AlgorithmFeedback.thy *)

theory HBDTranslationsUsingFeedback imports HBDTranslationProperties "Refinement"
begin
  
context BaseOperationVars
begin

  (*The nondeterministic Algorithm that uses the feedback, serial, and parallel operations*)
  definition "TranslateHBD = 
    while_stm (\<lambda> As . length As > 1)(
      [:As \<leadsto> As' . \<exists> Bs Cs . 1 < length Bs \<and> perm As (Bs @ Cs) \<and> As' = FB (Parallel_list Bs) # Cs:]
      \<sqinter>
      [:As \<leadsto> As' . \<exists> A B Bs . perm As (A # B # Bs) \<and> As' = (FB (FB A ;; FB B)) # Bs:]
     )
   o [-(\<lambda> As . FB(As ! 0))-]"


  lemma [simp]:"Suc 0 \<le> length As_init \<Longrightarrow>
    Hoare (\<lambda>As. in_out_equiv (FB (As ! 0)) (FB (Parallel_list As_init))) [-\<lambda>As. FB (As ! 0)-] (\<lambda>S. in_out_equiv S (FB (Parallel_list As_init)))"
    apply (rule hoare_update)
    by (simp add: le_fun_def)

  definition "invariant As_init n As = (length As = n \<and> io_distinct As \<and>  in_out_equiv (FB (Parallel_list As)) (FB (Parallel_list As_init)) \<and> n \<ge> 1)"

  lemma io_diagram_Parallel_list: "\<forall> A \<in> set As . io_diagram A \<Longrightarrow> distinct (concat (map Out As)) \<Longrightarrow> io_diagram (Parallel_list As)"
    proof (induction As)
    case Nil
    from Nil show ?case by simp
    next
    case (Cons A As)
    show ?case
      apply (simp)
      apply (rule io_diagram_Parallel)
      using Cons(2) apply simp
      using Cons apply simp
      using Cons(3) apply auto
      by (simp add: Out_Parallel)
    qed

  lemma io_diagram_Parallel_list_a: "io_distinct As \<Longrightarrow> io_diagram (Parallel_list As)"
    apply (rule_tac io_diagram_Parallel_list)
    by (simp_all add: io_distinct_def)


  thm Parallel_list_cons

  thm Parallel_assoc_gen

  thm ParallelId_left
  thm io_diagram_Parallel_list

lemma Parallel_list_append: "\<forall> A \<in> set As . io_diagram A \<Longrightarrow> distinct (concat (map Out As)) \<Longrightarrow> \<forall> A \<in> set Bs . io_diagram A 
      \<Longrightarrow> distinct (concat (map Out Bs))\<Longrightarrow> 
      Parallel_list (As @ Bs) = Parallel_list As ||| Parallel_list Bs"
    proof (induction As)
      case Nil
      from Nil show ?case
        apply (simp )
        apply (subst ParallelId_left, simp_all)
        by (rule io_diagram_Parallel_list, simp_all)
      next
      case (Cons A As)
      from Cons show ?case
        apply simp
        apply (subst Parallel_assoc_gen, simp_all)
        apply (rule io_diagram_Parallel_list, simp_all)
        by (rule io_diagram_Parallel_list, simp_all)
    qed
       
  primrec sequence :: "nat \<Rightarrow> nat list" where
    "sequence 0 = []" |
    "sequence (Suc n) = sequence n @ [n]"

  lemma "sequence (Suc (Suc 0)) = [0,1]"
    by auto

  lemma in_out_equiv_io_diagram[simp]: "in_out_equiv A B \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram A"
    apply (unfold io_diagram_def)
    apply (simp add:  in_out_equiv_def, safe)
    using dist_perm perm_sym apply blast
    using dist_perm perm_sym by blast

  thm comp_parallel_distrib

  lemma in_out_equiv_Parallel_cong_right: "io_diagram A \<Longrightarrow> io_diagram C \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> in_out_equiv B C 
    \<Longrightarrow> in_out_equiv (A ||| B) (A ||| C)"
    proof -
      assume "io_diagram A"
      from this have [simp]: "TVs (In A) = TI (Trs A)" and [simp]: " TVs (Out A) = TO (Trs A)" and [simp]: "distinct (In A)" and [simp]: "distinct (Out A)"
        by (unfold io_diagram_def, simp_all)
      assume A: "io_diagram C"
      from this have [simp]: "TVs (In C) = TI (Trs C)" and [simp]: " TVs (Out C) = TO (Trs C)" and [simp]: "distinct (In C)" and [simp]: "distinct (Out C)"
        by (unfold io_diagram_def, simp_all)
      assume "set (Out A) \<inter> set (Out B) = {}"
      assume B: "in_out_equiv B C"
      from this have [simp]: "perm (In B) (In C)" and [simp]: "perm (Out B) (Out C)" and [simp]: "Trs B = [In B \<leadsto> In C] oo Trs C oo [Out C \<leadsto> Out B]"
        by (simp_all add: in_out_equiv_def)

      from A and B have "io_diagram B"
        by simp
      from this have [simp]: "TVs (In B) = TI (Trs B)" and [simp]: " TVs (Out B) = TO (Trs B)" and [simp]: "distinct (In B)" and [simp]: "distinct (Out B)"
        by (unfold io_diagram_def, simp_all)

      have [simp]: "[In A \<oplus> In B \<leadsto> In A \<oplus> In C] oo ([In A \<oplus> In C \<leadsto> In A @ In C] oo (parallel (Trs A) (Trs C))) oo [Out A @ Out C \<leadsto> Out A @ Out B] = 
        [In A \<oplus> In B \<leadsto> In A \<oplus> In C] oo [In A \<oplus> In C \<leadsto> In A @ In C] oo parallel (Trs A) (Trs C) oo [Out A @ Out C \<leadsto> Out A @ Out B]"
        by (simp add: comp_assoc)
      have [simp]: "... = [In A \<oplus> In B \<leadsto> In A @ In C] oo parallel (Trs A) (Trs C) oo [Out A @ Out C \<leadsto> Out A @ Out B]"
         by (subst switch_comp, simp_all)
      have "[In A \<oplus> In B \<leadsto> In A @ In B] oo parallel (Trs A) ([In B \<leadsto> In C] oo Trs C oo [Out C \<leadsto> Out B]) 
          = [In A \<oplus> In B \<leadsto> In A @ In B] oo parallel ([In A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Out A]) ([In B \<leadsto> In C] oo Trs C oo [Out C \<leadsto> Out B])"
        by simp
      also have "... = [In A \<oplus> In B \<leadsto> In A @ In B] oo (
                    parallel [In A \<leadsto> In A] [In B \<leadsto> In C] oo parallel (Trs A) (Trs C) oo parallel [Out A \<leadsto> Out A] [Out C \<leadsto> Out B])"
        apply (subst comp_parallel_distrib [THEN sym])
        apply simp_all [2]
        apply (subst comp_parallel_distrib [THEN sym])
        by simp_all
      also have " ... =  [In A \<oplus> In B \<leadsto> In A @ In B] oo (
                   parallel [In A \<leadsto> In A] [In B \<leadsto> In C] oo parallel (Trs A) (Trs C) oo[Out A @ Out C \<leadsto> Out A @ Out B])"
        by (metis \<open>distinct (Out A)\<close> \<open>distinct (Out C)\<close> \<open>perm (Out B) (Out C)\<close> \<open>set (Out A) \<inter> set (Out B) = {}\<close> distinct_append order_refl par_switch perm_set_eq)
      also have "... = [In A \<oplus> In B \<leadsto> In A @ In B] oo parallel [In A \<leadsto> In A] [In B \<leadsto> In C] 
        oo parallel (Trs A) (Trs C) oo[Out A @ Out C \<leadsto> Out A @ Out B]"
        apply (subst comp_assoc, simp_all)
        apply (subst comp_assoc)
        apply (subst TI_par)
        using TI_switch TO_switch TVs_append apply presburger
        apply simp
        apply (subst comp_assoc)
        using TI_comp TI_par TI_switch TO_par TO_switch TVs_append \<open>TVs (In A) = TI (Trs A)\<close> \<open>TVs (In C) = TI (Trs C)\<close> apply presburger
        apply simp
        by (subst comp_assoc, simp_all)

     also have "... = [In A \<oplus> In B \<leadsto> In A @ In C] oo parallel (Trs A) (Trs C) oo[Out A @ Out C \<leadsto> Out A @ Out B]"
      by (simp add: Trs_Parallel_list_aux_b)
        
      finally show "in_out_equiv (A ||| B) (A ||| C)"
        by (simp add: in_out_equiv_def Parallel_def)
    qed

  lemma perm_map: "perm x y \<Longrightarrow> perm (map f x) (map f y)"
    by (simp add: perm_mset)


  lemma distinct_concat_perm: "\<And> Y . distinct (concat X) \<Longrightarrow> perm X Y \<Longrightarrow> distinct (concat Y)"
    proof (induction X)
      case Nil
      from Nil show ?case by simp
      next
      case (Cons a X)
      from Cons(3) obtain A B where [simp]: "Y = A @ a #B" and [simp]: "perm X (A @ B)"
        by (simp add: split_perm, blast)
      from Cons(1) have "distinct (concat X) \<Longrightarrow> perm X (A @ B) \<Longrightarrow> distinct (concat (A @ B)) "
        by blast
      from this and Cons(2) have A: "distinct (concat (A @ B))" by simp
      from Cons(2) have "distinct (concat X)" by simp
      from Cons(2) have [simp]: "distinct a" by simp
      have "set (X) = set (A @ B)"
        using \<open>perm X (A @ B)\<close> perm_set_eq by blast
      from this and Cons(2) show ?case
        using A apply simp
        by auto
    qed

  lemma distinct_Par_equiv_a: "\<And> Bs . \<forall> A \<in> set As . io_diagram A \<Longrightarrow> distinct (concat (map Out As)) \<Longrightarrow> perm As Bs \<Longrightarrow>
      in_out_equiv (Parallel_list As) (Parallel_list Bs)"
      
    proof (induction As)
      case Nil
      from  \<open>perm [] Bs\<close> show ?case
      apply (simp)
      by (rule in_out_equiv_refl, simp)
      next
      case (Cons A As)
      have "A \<in> set Bs"
        using Cons.prems(3) perm_set_eq by fastforce
      from this obtain Cs Ds where A: "Bs = Cs @ A # Ds"
        by (metis split_list)

      have [simp]: " perm As (Ds @ Cs)"
        using Cons(4) and A
          by (simp add: perm_mset)

        have [simp]: "\<forall> A \<in> set Cs . io_diagram A"
          using A Cons.prems(1) Cons.prems(3) perm_set_eq by fastforce
      have [simp]: "\<forall> A \<in> set Ds . io_diagram A"
          using A Cons.prems(1) Cons.prems(3) perm_set_eq by fastforce
      have B: "distinct (concat (map Out Bs))"
        apply (rule distinct_concat_perm)
        apply (rule  Cons(3))
        apply (rule perm_map)
        using Cons(4) by simp
      from this and A have [simp]: "distinct (concat (map Out Cs))"
        by simp
      from B and A have [simp]: "distinct (concat (map Out Ds))"
        by simp
      have [simp]: "io_diagram A"
        using Cons(2) by simp
      from this have [simp]: "distinct (Out A)"
        by (unfold io_diagram_def, simp)
      have [simp]: " io_diagram (Parallel_list Ds)"
        by (rule io_diagram_Parallel_list, simp_all)
      have [simp]: "io_diagram (Parallel_list Cs)"
        by (rule io_diagram_Parallel_list, simp_all)
      have [simp]: "set (Out A) \<inter> set (Out (Parallel_list As)) = {}"
        using Cons(3) by (simp add: Out_Parallel)
      have [simp]: "\<forall> A \<in> set As . io_diagram A"
        using Cons(2) by simp
      have [simp]:"distinct (concat (map Out As))"
        using Cons(3) by simp

      from B and A have [simp]: "set (Out A) \<inter> (\<Union>a\<in>set Ds. set (Out a)) = {}"
        by simp
      have [simp]: "set (Out A) \<inter> set (Out (Parallel_list Ds)) = {}"
        by (simp add: Out_Parallel)

      from B and A have [simp]: "set (Out (Parallel_list Ds)) \<inter> set (Out (Parallel_list Cs)) = {}"
        by (simp add: Out_Parallel, auto)

      from B and A have [simp]: "set (Out (Parallel_list Cs)) \<inter> set (Out A) = {}"
        by (simp add: Out_Parallel)

     from B and A have [simp]: "set (Out (Parallel_list Cs)) \<inter> set (Out (Parallel_list Ds)) = {}"
        by (simp add: Out_Parallel)

     from B and A have [simp]:"(set (Out A) \<union> set (Out (Parallel_list Ds))) \<inter> set (Out (Parallel_list Cs)) = {}"
        by (simp add: Out_Parallel, auto)
      have [simp]:"io_diagram (A ||| Parallel_list Ds)"
        by (rule io_diagram_Parallel, simp_all)
      from Cons(1)
        have "in_out_equiv (Parallel_list As) (Parallel_list (Ds @ Cs))"
        by simp
      from this have [simp]: "in_out_equiv (Parallel_list As) (Parallel_list Ds ||| (Parallel_list Cs))"
        by (simp add: Parallel_list_append)
      have [simp]:"io_diagram (Parallel_list Ds ||| Parallel_list Cs)"
        by (rule io_diagram_Parallel, simp_all)
      have [simp]: "io_diagram (Parallel_list As)"
        by (rule io_diagram_Parallel_list, simp_all)
      have [simp]: "io_diagram (A ||| Parallel_list As)"
        by (rule io_diagram_Parallel, simp_all)
      have [simp]: "io_diagram (A ||| Parallel_list Ds ||| Parallel_list Cs)"
        by (rule io_diagram_Parallel, simp_all)
      have [simp]: "io_diagram (Parallel_list Cs ||| (A ||| Parallel_list Ds))"
        by (rule io_diagram_Parallel, simp_all)

       from A show ?case
        apply (simp_all add: Parallel_list_append)
        apply (rule_tac B = "(A ||| Parallel_list Ds) ||| Parallel_list Cs" in in_out_equiv_tran, simp_all)
        apply (subst Parallel_assoc_gen, simp_all)
        apply (rule in_out_equiv_Parallel_cong_right, simp_all)
        by (rule in_out_equiv_Parallel, simp_all)
    qed

  thm distinct_concat_perm
  thm perm_map

  lemma distinct_FB: "distinct (In A) \<Longrightarrow> distinct (In (FB A))"
    by (simp add: FB_def Let_def)

  lemma io_distinct_FB_cat: "io_distinct (A # Cs) \<Longrightarrow> io_distinct (FB A # Cs)"
    apply (simp add: io_distinct_def)
    apply safe
    apply (simp_all add: FB_def Let_def set_diff) [4]
    apply auto [2]
    by (rule Type_ok_FB, simp)

  lemma io_distinct_perm: "io_distinct As \<Longrightarrow> perm As Bs \<Longrightarrow> io_distinct Bs"
    apply (simp add: io_distinct_def)
    apply safe
    apply (rule distinct_concat_perm)
    apply (simp_all)
    apply (rule perm_map, simp)
    apply (rule_tac X = "map Out As" in distinct_concat_perm, simp_all)
     apply (rule perm_map, simp)
      using perm_set_eq by blast

  lemma [simp]: "distinct (concat X) \<Longrightarrow> op_list [] (\<oplus>) (X) = concat X"
    apply (induction X, simp_all)
    by (simp add: addvars_distinct)

  lemma [simp]: "io_distinct As \<Longrightarrow> perm As (Bs @ Cs) \<Longrightarrow> io_distinct (FB (Parallel_list Bs) # Cs)"
    apply (rule io_distinct_FB_cat)
    apply (drule_tac Bs = "Bs @ Cs" in io_distinct_perm, simp_all)
    apply (simp add: io_distinct_def In_Parallel Out_Parallel)
    apply safe
    by (rule io_diagram_Parallel_list, simp_all)

  lemma io_distinct_append_a: "io_distinct As \<Longrightarrow> perm As (Bs @ Cs) \<Longrightarrow> io_distinct Bs"
    apply (drule_tac Bs = "Bs @ Cs" in io_distinct_perm, simp_all)
    by (simp add: io_distinct_def)

  lemma io_distinct_append_b: "io_distinct As \<Longrightarrow> perm As (Bs @ Cs) \<Longrightarrow> io_distinct Cs"
    apply (drule_tac Bs = "Bs @ Cs" in io_distinct_perm, simp_all)
    by (simp add: io_distinct_def)

  lemma [simp]: "io_distinct As \<Longrightarrow> perm As (Bs @ Cs) \<Longrightarrow> io_diagram (FB (FB (Parallel_list Bs) ||| Parallel_list Cs))"
    apply (rule Type_ok_FB)
    apply (rule io_diagram_Parallel)
    apply (rule Type_ok_FB)
    apply (drule io_distinct_append_a, simp_all)
    apply (simp add: io_diagram_Parallel_list_a)
    apply (drule io_distinct_append_b, simp_all)
    apply (simp add: io_diagram_Parallel_list_a)
    apply (subgoal_tac " set (Out ((Parallel_list Bs))) \<inter> set (Out (Parallel_list Cs)) = {}")
    apply (subgoal_tac "set (Out (FB (Parallel_list Bs))) \<subseteq> set (Out ((Parallel_list Bs)))")
    apply auto [1]
    apply (simp add: FB_def Let_def)
    apply (simp add: Out_Parallel)
    apply (drule io_distinct_perm, simp_all)
    by (simp add: io_distinct_def)

  lemma [simp]: "io_distinct As \<Longrightarrow> io_diagram (FB (Parallel_list As))"
    apply (rule Type_ok_FB)
    by (simp add: io_diagram_Parallel_list_a)

  lemma io_distinct_set_In[simp]: " io_distinct x \<Longrightarrow>  perm x (A # B # Bs) \<Longrightarrow> set (In A) \<inter> set (In B) = {}"
    apply (drule io_distinct_perm, simp_all)
    by (simp add: io_distinct_def)

  lemma io_distinct_set_Out[simp]: " io_distinct x \<Longrightarrow>  perm x (A # B # Bs) \<Longrightarrow> set (Out A) \<inter> set (Out B) = {}"
    apply (drule io_distinct_perm, simp_all)
    by (simp add: io_distinct_def)

  lemma distinct_Par_equiv_b: "io_distinct As  \<Longrightarrow> perm As (Bs @ Cs) \<Longrightarrow> in_out_equiv (FB (FB (Parallel_list Bs) ||| Parallel_list Cs)) (FB (Parallel_list As))"
    proof -
      assume [simp]: "io_distinct As"
      assume [simp]: "perm As (Bs @ Cs)"
      have [simp]: "io_diagram (Parallel_list Bs)"
        apply (rule io_diagram_Parallel_list_a)
        by (rule_tac As = As and Cs = Cs in io_distinct_append_a, simp_all)
      have [simp]: "io_diagram (FB (Parallel_list Bs))"
        by (rule Type_ok_FB, simp)
      have [simp]: "io_diagram (Parallel_list Cs)"
        apply (rule io_diagram_Parallel_list_a)
        by (rule_tac As = As and Bs = Bs in io_distinct_append_b, simp_all)
      have [simp]: "(\<Union>a\<in>set Bs. set (Out a)) \<inter> (\<Union>a\<in>set Cs. set (Out a)) = {}"
        apply (cut_tac As = As and Bs = "Bs @ Cs" in io_distinct_perm, simp_all)
        by (simp add: io_distinct_def)
      have Aa[simp]: "set (In (Parallel_list Bs)) \<inter> set (In (Parallel_list Cs)) = {}"
        apply (simp add: In_Parallel)
        apply (cut_tac As = As and Bs = "Bs @ Cs" in io_distinct_perm, simp_all)
        by (simp add: io_distinct_def)
      have Ab[simp]: "set (Out (Parallel_list Bs)) \<inter> set (Out (Parallel_list Cs)) = {}"
        by (simp add: Out_Parallel)
      have [simp]: "set (In (FB (Parallel_list Bs))) \<inter> set (In (Parallel_list Cs)) = {}"
        apply (subgoal_tac "set (In ((Parallel_list Bs))) \<inter> set (In (Parallel_list Cs)) = {}")
        apply (subgoal_tac "set (In (FB (Parallel_list Bs))) \<subseteq> set (In ((Parallel_list Bs)))")
        apply (auto simp del: Aa) [1]
        by (auto simp add: FB_def Let_def set_diff)
 
      have [simp]: "set (Out (FB (Parallel_list Bs))) \<inter> set (Out (Parallel_list Cs)) = {}"
        apply (subgoal_tac "set (Out ((Parallel_list Bs))) \<inter> set (Out (Parallel_list Cs)) = {}")
        apply (subgoal_tac "set (Out (FB (Parallel_list Bs))) \<subseteq> set (Out ((Parallel_list Bs)))")
        apply (auto simp del: Ab) [1]
        by (auto simp add: FB_def Let_def set_diff)

      have [simp]:"Ball (set Bs) io_diagram"
        apply (cut_tac As = As and Bs = Bs and Cs = Cs in io_distinct_append_a, simp_all)
        by (simp add: io_distinct_def)
      have [simp]:"Ball (set Cs) io_diagram"
        apply (cut_tac As = As and Bs = Bs and Cs = Cs in io_distinct_append_b, simp_all)
        by (simp add: io_distinct_def)
      have [simp]:" distinct (concat (map Out Bs))"
        apply (cut_tac As = As and Bs = Bs and Cs = Cs in io_distinct_append_a, simp_all)
        by (simp add: io_distinct_def)
      have [simp]:"distinct (concat (map Out Cs))"
        apply (cut_tac As = As and Bs = Bs and Cs = Cs in io_distinct_append_b, simp_all)
        by (simp add: io_distinct_def)
      have [simp]:"io_diagram (Parallel_list As)"
        by (simp add: io_diagram_Parallel_list_a)
      have A: "FB (FB (Parallel_list Bs) ;; FB (Parallel_list Cs)) = FB (Parallel_list Bs ||| Parallel_list Cs)"
        by (subst FeedbackSerial, simp_all)
      show ?thesis
        apply (subst FeedbackSerial, simp_all)
        apply (subst FB_idemp, simp_all)
        apply (simp add:  A)
        apply (subst Parallel_list_append [THEN sym], simp_all)
        apply (rule in_out_equiv_FB, simp_all)
        apply (rule distinct_Par_equiv_a, simp_all)
        apply auto [1]
        by (simp add: perm_sym)
   qed


  lemma distinct_Par_equiv: "io_distinct As_init \<Longrightarrow> Suc 0 \<le> length As_init \<Longrightarrow>
    length As = w \<Longrightarrow> io_distinct As \<Longrightarrow> in_out_equiv (FB (Parallel_list As)) (FB (Parallel_list As_init)) \<Longrightarrow>
    Suc 0 < w \<Longrightarrow> Suc 0 < length Bs \<Longrightarrow> perm As (Bs @ Cs) \<Longrightarrow> 
      io_distinct (FB (Parallel_list Bs) # Cs) \<and> in_out_equiv (FB (FB (Parallel_list Bs) ||| Parallel_list Cs)) (FB (Parallel_list As_init))"
    apply simp
    apply (rule_tac B = "FB (Parallel_list As)" in in_out_equiv_tran, simp_all)
    by (rule distinct_Par_equiv_b, simp_all)

lemma AAAA_x[simp]: "io_distinct As_init \<Longrightarrow> Suc 0 \<le> length As_init \<Longrightarrow> invariant As_init w x \<Longrightarrow> Suc 0 < length x \<Longrightarrow> Suc 0 < length Bs 
        \<Longrightarrow> perm x (Bs @ Cs) 
        \<Longrightarrow> invariant As_init (Suc (length Cs)) (FB (Parallel_list Bs) # Cs)"
    by (simp add: invariant_def, safe, simp_all add: distinct_Par_equiv)

  term "{1,2,3} - {2,3}"

  thm ParallelId_right

  lemma [simp]: "io_distinct As_init \<Longrightarrow>
                Suc 0 \<le> length As_init \<Longrightarrow> invariant As_init w x \<Longrightarrow> Suc 0 < length x \<Longrightarrow> perm x (A # B # Bs) 
                \<Longrightarrow> invariant As_init (Suc (length Bs)) (FB (FB A ;; FB B) # Bs)"
     apply (subst FeedbackSerial [THEN sym])
     apply (simp_all add: invariant_def)
     apply (drule perm_set_eq, simp add: io_distinct_def) 
     apply (drule perm_set_eq, simp add: io_distinct_def)
     apply (rule io_distinct_set_In, simp_all)
     apply (rule io_distinct_set_Out, simp_all)
     apply (cut_tac Bs = "[A,B]" and Cs = Bs and w = w in AAAA_x, simp_all)
     apply (simp add: invariant_def)
     apply (simp add: invariant_def)
     apply (subst (asm) ParallelId_right, simp_all)
     apply (drule perm_set_eq, simp add: io_distinct_def) 
     apply (subst (asm) ParallelId_right, simp_all)
     by (drule perm_set_eq, simp add: io_distinct_def) 

  lemma [simp]: "io_distinct As_init \<Longrightarrow> Suc 0 \<le> length As_init \<Longrightarrow>
         Hoare (invariant As_init w \<sqinter> (\<lambda>As. Suc 0 < length As)) 
          [:As\<leadsto>As'.\<exists>Bs. Suc 0 < length Bs \<and> (\<exists>Cs. perm As (Bs @ Cs) \<and> As' = FB (Parallel_list Bs) # Cs):] (Sup_less (invariant As_init) w)"
     apply (rule hoare_demonic, safe)
     apply (simp add: Sup_less_def)
     apply (rule_tac x = "invariant As_init (Suc (length Cs))" in exI, safe)
     apply (rule_tac x = "(Suc (length Cs))" in exI, simp_all)
     apply (simp add: invariant_def, safe)
     by (drule perm_length, simp)

  lemma [simp]: "io_distinct As_init \<Longrightarrow> Suc 0 \<le> length As_init \<Longrightarrow>
         Hoare (invariant As_init w \<sqinter> (\<lambda>As. Suc 0 < length As)) 
          [:As\<leadsto>As'.\<exists>A B Bs. perm As (A # B # Bs) \<and> As' = FB (FB A ;; FB B) # Bs:] (Sup_less (invariant As_init) w)"
     apply (rule hoare_demonic, safe)
     apply (simp add: Sup_less_def)
     apply (rule_tac x = "invariant As_init (Suc (length Bs))" in exI, safe)
     apply (rule_tac x = "(Suc (length Bs))" in exI, simp_all)
     apply (simp add: invariant_def, safe)
     apply (drule perm_length, simp)
     done

  theorem CorrectnessTranslateHBD: "io_distinct As_init \<Longrightarrow> length As_init \<ge> 1 \<Longrightarrow> 
    Hoare (io_distinct \<sqinter> (\<lambda> As . As = As_init)) TranslateHBD (\<lambda> S . in_out_equiv S (FB (Parallel_list As_init)))"
    apply (simp add: TranslateHBD_def)
    apply (simp add: hoare_sequential)
    apply (rule_tac x = "\<lambda> As . in_out_equiv (FB (As ! 0)) (FB (Parallel_list As_init))" in exI)
    apply simp
    apply (rule_tac p = "invariant As_init" in hoare_while_a, simp_all)
    apply (simp add: hoare_choice, safe)
    apply (simp_all add: invariant_def, safe)
    apply (rule in_out_equiv_refl)
    apply (rule Type_ok_FB)
    apply (rule io_diagram_Parallel_list_a, simp)
    apply (case_tac x, simp)
    apply clarify
    proof -
      fix a list
      assume B: "in_out_equiv (FB (Parallel_list (a # list))) (FB (Parallel_list As_init))"
      assume A: "io_distinct (a # list)"
      assume "Suc 0 = length (a # list)"
      from this have [simp]: "list = []"
        by simp
      from A have [simp]: "io_diagram a"
        by (simp add: io_distinct_def)
      have [simp]: "FB (Parallel_list (a # list)) = FB a"
        by simp
      from B show "in_out_equiv (FB ((a # list) ! 0)) (FB (Parallel_list As_init))"
        by simp
    qed
 end
  
end