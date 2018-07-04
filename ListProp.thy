section{*\label{sec_ListProp}List Operations. Permutations and Substitutions*}

theory ListProp imports Main "~~/src/HOL/Library/Permutation"
begin
  
lemma perm_mset: "perm x y = (mset x = mset y)"
  by (simp add: mset_eq_perm)

lemma perm_tp: "perm (x@y) (y@x)"
  by (simp add: perm_mset union_commute)

  lemma perm_union_left: "perm x z \<Longrightarrow> perm (x @ y) (z @ y)"
    by (simp add: perm_mset)

  lemma perm_union_right: "perm x z \<Longrightarrow> perm (y @ x) (y @ z)"
    by (simp add: perm_mset)

  lemma perm_trans: "perm x y \<Longrightarrow> perm y z \<Longrightarrow> perm x z"
    by (simp add: perm_mset)

  lemma perm_sym: "perm x y \<Longrightarrow> perm y x"
    by (simp add: perm_mset)

  lemma perm_length: "perm u v \<Longrightarrow> length u = length v"
    by (metis perm_mset size_mset)

   lemma perm_set_eq: "perm x y \<Longrightarrow> set x = set y"
     by (metis perm_mset set_mset_mset)
       
     lemma perm_empty[simp]: "(perm [] v) = (v = [])" and "(perm v []) = (v = [])"
       by (simp_all add: perm_mset)
         
      lemma perm_refl[simp]: "perm x x"
        by (simp add: perm_mset)


  lemma dist_perm: "\<And> y . distinct x \<Longrightarrow> perm x y \<Longrightarrow> distinct y"
    by (metis card_distinct distinct_card mset_eq_setD perm_mset perm_length )


      lemma split_perm: "perm (a # x) x' = (\<exists> y y' . x' = y @ a # y' \<and> perm x (y @ y'))"
        apply safe
        apply (subgoal_tac "\<exists> y y' .  x' = y @ a # y'")
        apply safe
        apply (rule_tac x = y in exI)
        apply (rule_tac x = y' in exI, simp_all)
          apply (simp add: perm_mset)
        apply (drule perm_set_eq)
        apply (simp add: set_eq_iff)
        using split_list apply fastforce
          by (simp add: perm_mset)

  fun subst:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
    "subst [] [] c = c" |
    "subst (a#x) (b#y) c = (if a = c then b else subst x y c)" |
    "subst x y c = undefined"

  lemma subst_notin [simp]: "\<And> y . length x = length y \<Longrightarrow> a \<notin> set x \<Longrightarrow> subst x y a = a"
    apply (induction x, simp_all)
    by (metis Suc_length_conv subst.simps(2))

  lemma subst_cons_a:"\<And> y . distinct x \<Longrightarrow> a \<notin> set x \<Longrightarrow> b \<notin> set x \<Longrightarrow> length x = length y \<Longrightarrow>  subst (a # x) (b # y) c =  (subst x y (subst [a] [b] c))"
    by simp

  lemma subst_eq: "subst x x y = y"
    apply (induct x) 
    by (auto) 

  fun Subst :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "Subst x y [] = []" |
    "Subst x y (a # z) = subst x y a # (Subst x y z)"

  lemma Subst_empty[simp]: "Subst [] [] y = y"
    apply (induct y) 
    by (auto) 

  (*todo: make simp*)
  lemma Subst_eq: "Subst x x y = y"
    apply (induction y)
    by (simp_all add: subst_eq)


  lemma Subst_append: "Subst a b (x@y) = Subst a b x @ Subst a b y"
    by (induction x, simp_all)

  lemma Subst_notin[simp]: "a \<notin> set z \<Longrightarrow> Subst (a # x) (b # y) z = Subst x y z"
    by (induction z, simp_all)

  lemma Subst_all[simp]: "\<And> v . distinct u \<Longrightarrow>length u = length v \<Longrightarrow> Subst u v u = v"
    apply (induction u, simp_all)
    by (case_tac v, simp_all)
    
  lemma Subst_inex[simp]: "\<And> b. set a \<inter> set x = {} \<Longrightarrow> length a = length b \<Longrightarrow> Subst a b x = x"
    apply (induction a, simp_all)
    by (metis Subst_notin Suc_length_conv)
  
  lemma set_Subst: "set (Subst [a] [b] x) = (if a \<in> set x then (set x - {a}) \<union> {b} else set x)"
    apply (induction x)
    by auto

  lemma distinct_Subst: "distinct (b#x) \<Longrightarrow> distinct (Subst [a] [b] x)"
    apply (induction x)
    apply simp_all
    by (auto simp add: set_Subst)
        
  lemma inter_Subst: "distinct(b#y) \<Longrightarrow> set x \<inter> set y = {} \<Longrightarrow> b \<notin> set x \<Longrightarrow> set x \<inter> set (Subst [a] [b] y) = {}"
    apply (induction y)
    by simp_all

  lemma incl_Subst: "distinct(b#x) \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set (Subst [a] [b] y) \<subseteq> set (Subst [a] [b] x)"
    apply safe
    apply (simp add: set_Subst less_eq_set_def le_fun_def, auto)
    apply (case_tac "a \<in> set y", simp_all)
    apply (metis DiffE Diff_insert_absorb UnE singletonI)
    by meson

  lemma subst_in_set: "\<And>y. length x = length y \<Longrightarrow> a \<in> set x \<Longrightarrow> subst x y a \<in> set y"
    apply (induction x, auto)
    apply (case_tac y, simp_all)
    by (case_tac y, simp_all)


  lemma Subst_set_incl: "length x = length y \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set (Subst x y z) \<subseteq> set y"
    apply (induction z, auto)
    by (simp add: subst_in_set)

  lemma subst_not_in: "\<And> y . a \<notin> set x' \<Longrightarrow> length x = length y \<Longrightarrow> length x' = length y' \<Longrightarrow> subst (x @ x') (y @ y') a = subst x y a"
    apply (induction x, simp_all)
    by (case_tac y, simp_all)
    
  lemma subst_not_in_b: "\<And> y . a \<notin> set x \<Longrightarrow> length x = length y \<Longrightarrow> length x' = length y' \<Longrightarrow> subst (x @ x') (y @ y') a = subst x' y' a"
    apply (induction x, simp_all)
    by (case_tac y, simp_all, auto)

  lemma Subst_not_in: "set x' \<inter> set z = {} \<Longrightarrow> length x = length y \<Longrightarrow> length x' = length y' \<Longrightarrow> Subst (x @ x') (y @ y') z = Subst x y z"
    apply (induction z, simp_all)
    by (simp add: subst_not_in)

  lemma Subst_not_in_a: "set x \<inter> set z = {} \<Longrightarrow> length x = length y \<Longrightarrow> length x' = length y' \<Longrightarrow> Subst (x @ x') (y @ y') z = Subst x' y' z"
    apply (induction z, simp_all)
    by (simp add: subst_not_in_b)

  lemma subst_cancel_right [simp]: "\<And> y z . set x \<inter> set y = {} \<Longrightarrow> length y = length z \<Longrightarrow> subst (x @ y) (x @ z) a = subst y z a"
    by (induction x, simp_all, safe, simp)
    
  lemma Subst_cancel_right: "set x \<inter> set y = {} \<Longrightarrow> length y = length z \<Longrightarrow> Subst (x @ y) (x @ z) w = Subst y z w"
    by (induction w, simp_all)

  lemma subst_cancel_left [simp]: "\<And> y z . set x \<inter> set z = {} \<Longrightarrow> length x = length y \<Longrightarrow> subst (x @ z) (y @ z) a = subst x y a"
    apply (induction x, simp_all, safe, simp)
    apply (simp add: subst_eq)
    by (case_tac y, simp_all)

  lemma Subst_cancel_left: "set x \<inter> set z = {} \<Longrightarrow> length x = length y \<Longrightarrow> Subst (x @ z) (y @ z) w = Subst x y w"
    by (induction w, simp_all)


  lemma Subst_cancel_right_a: "a \<notin>  set y \<Longrightarrow> length y = length z \<Longrightarrow> Subst (a # y) (a # z) w = Subst y z w"
    apply (cut_tac x = "[a]" in Subst_cancel_right)
    by (simp_all)

  lemma subst_subst_id [simp]: "\<And> y . a \<in> set y \<Longrightarrow> distinct x \<Longrightarrow> length x = length y \<Longrightarrow> subst x y (subst y x a) = a"
    apply (induction x, simp_all)
    apply (case_tac y, simp_all, auto)
    by (simp add: subst_in_set)

  lemma Subst_Subst_id[simp]: "set z \<subseteq> set y \<Longrightarrow> distinct x \<Longrightarrow> length x = length y \<Longrightarrow> Subst x y (Subst y x z) = z"
    by (induction z, simp_all)

  lemma Subst_cons_aux_a: "set x \<inter> set y = {} \<Longrightarrow> distinct y \<Longrightarrow> length y = length z \<Longrightarrow> Subst (x @ y) (x @ z) y = z"
    apply (induction x)
    by simp_all

  lemma Subst_set_empty [simp]: "set z \<inter> set x = {} \<Longrightarrow> length x = length y \<Longrightarrow> Subst x y z = z"
    by (induction z, simp_all)

  lemma length_Subst[simp]: "length (Subst x y z) = length z"
    by (induction z, simp_all)


  lemma subst_Subst: "\<And> y y' . length y = length y' \<Longrightarrow> a \<in> set w \<Longrightarrow> subst w (Subst y y' w) a = subst y y' a"
    by (induction w, simp_all, auto)

  lemma Subst_Subst: "length y = length y' \<Longrightarrow> set z \<subseteq> set w \<Longrightarrow> Subst w (Subst y y' w) z = Subst y y' z"
    by (induction z, simp_all add: subst_Subst)
    
  (*to sort*)
  
  primrec listinter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<otimes>" 60) where
    "[] \<otimes> y = []" |
    "(a # x) \<otimes> y = (if a \<in> set y then a # (x \<otimes> y) else x \<otimes> y)"

  lemma inter_filter: "x \<otimes> y = filter (\<lambda> a . a \<in> set y) x"
    by (induction x, simp_all)

  lemma inter_append: "set y \<inter> set z = {} \<Longrightarrow> perm (x \<otimes> (y @ z)) ((x \<otimes> y) @ (x \<otimes> z))"
    apply (induction x, simp_all add: perm_mset)
    apply safe
    by blast

  lemma append_inter: "(x @ y) \<otimes> z = (x \<otimes> z) @ (y \<otimes> z)"
    by (induction x, simp_all)

  lemma notin_inter [simp]: "a \<notin> set x \<Longrightarrow> a \<notin> set (x \<otimes> y)"
    by (induction x, simp_all)

  lemma distinct_inter: "distinct x \<Longrightarrow> distinct (x \<otimes> y)"
    by (induction x, simp_all)

  lemma set_inter: "set (x \<otimes> y) = set x \<inter> set y"
    by (induction x, simp_all)


  primrec diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<ominus>" 52) where
    "[] \<ominus> y = []" |
    "(a # x) \<ominus> y = (if a \<in> set y then x \<ominus> y else a # (x \<ominus> y))"

  lemma diff_filter: "x \<ominus> y = filter (\<lambda> a . a \<notin> set y) x"
    by (induction x, simp_all)

  lemma diff_distinct: "set x \<inter> set y = {} \<Longrightarrow> (y \<ominus> x) = y"
    by (induction y, simp_all)

  lemma set_diff: "set (x \<ominus> y) = set x - set y"
    by (induction x, simp_all, auto)

  lemma distinct_diff: "distinct x \<Longrightarrow> distinct (x \<ominus> y)"
    by (induction x, simp_all add: set_diff)


  definition addvars :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<oplus>" 55) where
    "addvars x y = x @ (y \<ominus> x)"

  lemma addvars_distinct: "set x \<inter> set y = {} \<Longrightarrow> x \<oplus> y = x @ y"
    by (simp add: addvars_def diff_distinct)

  lemma set_addvars: "set (x \<oplus> y) = set x \<union> set y"
    by (simp add: addvars_def set_diff)

  lemma distinct_addvars: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> distinct (x \<oplus> y)"
    apply (simp add: addvars_def, induction x, simp_all)
    apply (simp add: distinct_diff)
    by (simp add: Diff_Int_distrib distinct_diff set_diff)

  lemma mset_inter_diff: "mset oa = mset (oa \<otimes> ia) + mset (oa \<ominus> (oa \<otimes> ia))"
    apply (simp add: inter_filter diff_filter)
    by (metis (mono_tags, lifting) filter_cong mset_compl_union)

  lemma diff_inter_left: "(x \<ominus> (x \<otimes> y)) = (x \<ominus> y)"
    apply (simp add: diff_filter inter_filter)
    by (metis (no_types, lifting) filter_cong)

  lemma diff_inter_right: "(x \<ominus> (y \<otimes> x)) = (x \<ominus> y)"
    apply (simp add: diff_filter inter_filter)
    by (metis (no_types, lifting) filter_cong)

  lemma addvars_minus: "(x \<oplus> y) \<ominus> z = (x \<ominus> z) \<oplus> (y \<ominus> z)"
    apply (simp add: diff_filter addvars_def)
    by (metis)
   
  lemma addvars_assoc: "x \<oplus> y \<oplus> z = x \<oplus> (y \<oplus> z)"
    apply (simp add: addvars_def diff_filter)
    by metis

  lemma diff_sym: "(x \<ominus> y \<ominus> z) = (x \<ominus> z \<ominus> y)"
    apply (simp add: diff_filter)
    by metis
   
  lemma diff_union: "(x \<ominus> y @ z) = (x \<ominus> y \<ominus> z)"
    by (simp add: diff_filter)

  lemma diff_notin: "set x \<inter> set z = {} \<Longrightarrow> (x \<ominus> (y \<ominus> z)) = (x \<ominus> y)"
    apply (simp add: diff_filter disjoint_iff_not_equal)
    by (metis (no_types, lifting) filter_cong)

  lemma union_diff: "x @ y \<ominus> z = ((x \<ominus> z) @ (y \<ominus> z))"
    by (simp add: diff_filter)

  lemma diff_inter_empty: "set x \<inter> set y = {} \<Longrightarrow> x \<ominus> y \<otimes> z = x"
    apply (simp add: diff_filter inter_filter)
    by (metis (no_types, lifting) disjoint_iff_not_equal filter_True)

  lemma inter_diff_empty: "set x \<inter> set z = {} \<Longrightarrow> x \<otimes> (y \<ominus> z) = (x \<otimes> y)"
    apply (simp add: diff_filter inter_filter)
    by (metis (no_types, lifting) disjoint_iff_not_equal filter_cong)

  lemma inter_diff_distrib: "(x \<ominus> y) \<otimes> z = ((x \<otimes> z) \<ominus> (y \<otimes> z))"
    apply (simp add: diff_filter inter_filter)
    by (metis)

  lemma diff_emptyset: "x \<ominus> [] = x"
    by (simp add: diff_filter)

  lemma diff_eq: "x \<ominus> x = []"
    by (simp add: diff_filter)

  lemma diff_subset: "set x \<subseteq> set y \<Longrightarrow> x \<ominus> y = []"
    by (metis Diff_eq_empty_iff set_diff set_empty)

  lemma empty_inter: "set x \<inter> set y = {} \<Longrightarrow> x \<otimes> y = []"
    by (metis set_empty set_inter)

  lemma empty_inter_diff: "set x \<inter> set y = {} \<Longrightarrow> x \<otimes> (y \<ominus> z) = []"
    apply (simp add: inter_filter diff_filter)
    by (metis (no_types, lifting) disjoint_iff_not_equal filter_False)

  lemma inter_addvars_empty: "set x \<inter> set z = {} \<Longrightarrow> x \<otimes> y @ z = x \<otimes> y"
    apply (simp add: inter_filter)
    by (metis (no_types, lifting) disjoint_iff_not_equal filter_cong)

  lemma diff_disjoint: "set x \<inter> set y = {} \<Longrightarrow> x \<ominus> y = x"
    by (metis diff_distinct inter_filter inter_set_filter set_inter)
    
      lemma addvars_empty[simp]: "x \<oplus> [] = x"
        by (simp add: addvars_def)

      lemma empty_addvars[simp]: "[] \<oplus> x = x"
        apply (induction x, simp_all)
        by (simp add: addvars_def)


  lemma distrib_diff_addvars: "x \<ominus> (y @ z) = ((x \<ominus> y) \<otimes> (x \<ominus> z))"
    apply (simp add: diff_filter inter_filter)
    by (metis diff_filter diff_inter_left filter_True filter_filter inter_diff_distrib inter_filter inter_set_filter set_inter)

  lemma inter_subset: "x \<otimes> (x \<ominus> y) = (x \<ominus> y)"
    by (metis diff_emptyset diff_union distrib_diff_addvars)

  lemma diff_cancel: "x \<ominus> y \<ominus> (z \<ominus> y) = (x \<ominus> y \<ominus> z)"
    by (simp add: diff_notin inf_commute set_diff)

  lemma diff_cancel_set: "set x \<inter> set u = {} \<Longrightarrow> x \<ominus> y \<ominus> (z \<ominus> u) = (x \<ominus> y \<ominus> z)"
    by (metis diff_notin diff_sym)

  lemma inter_subset_l1: "\<And> y. distinct x \<Longrightarrow> length y = 1 \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> x \<otimes> y = y"
    apply (induction x, simp_all)
    apply safe
    apply (metis (no_types, lifting) Diff_insert_absorb Int_insert_left_if0 Suc_length_conv empty_inter empty_iff inf.orderE inf_commute length_0_conv list.set(1) list.simps(15) singletonD subset_insert_iff)
    by auto

  lemma perm_diff_left_inter: "perm (x \<ominus> y) (((x \<ominus> y) \<otimes> z) @ ((x \<ominus> y) \<ominus> z))"
    apply (simp add: diff_filter inter_filter perm_mset)
    by (metis filter_filter mset_compl_union)
    
  lemma perm_diff_right_inter: "perm (x \<ominus> y) (((x \<ominus> y) \<ominus> z) @ ((x \<ominus> y) \<otimes> z))"  
    by (metis perm_mset perm_diff_left_inter perm_tp)      


  lemma perm_switch_aux_a: "perm x ((x \<ominus> y) @ (x \<otimes> y))"
    by (metis diff_emptyset perm_diff_right_inter)

  lemma perm_switch_aux_b: "perm (x @ (y \<ominus> x)) ((x \<ominus> y) @ (x \<otimes> y) @ (y \<ominus> x))"
    by (metis perm_switch_aux_a append_assoc mset_append perm_mset)

  lemma perm_switch_aux_c: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm ((y \<otimes> x) @ (y \<ominus> x)) y"
    by (metis perm_switch_aux_a perm_mset perm_tp)

  lemma perm_switch_aux_d: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm (x \<otimes> y) (y \<otimes> x)"
    by (metis distinct_inter inf.commute perm_mset set_eq_iff_mset_eq_distinct set_inter)
     
  lemma perm_switch_aux_e: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm ((x \<otimes> y) @ (y \<ominus> x)) ((y \<otimes> x) @ (y \<ominus> x))"
    by (simp add: perm_union_left perm_switch_aux_d)

  lemma perm_switch_aux_f: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm ((x \<otimes> y) @ (y \<ominus> x)) y"
    apply (cut_tac x="((x \<otimes> y) @ (y \<ominus> x))"  and y ="((y \<otimes> x) @ (y \<ominus> x))" and z="y" in perm_trans)
      apply (simp add: perm_switch_aux_e)
      apply (simp add: perm_switch_aux_d)
    apply (simp add: perm_switch_aux_c)
    by simp
      
  lemma perm_switch_aux_h: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm ((x \<ominus> y) @ (x \<otimes> y) @ (y \<ominus> x)) ((x \<ominus> y) @ y)"
    by (simp add: perm_union_right perm_switch_aux_f)

  lemma perm_switch: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm (x @ (y \<ominus> x)) ((x \<ominus> y) @ y)"
    apply (cut_tac x="(x @ (y \<ominus> x))"  and y ="((x \<ominus> y) @ (x \<otimes> y) @ (y \<ominus> x))" and z="((x \<ominus> y) @ y)" in perm_trans)
      apply (simp add: perm_switch_aux_b)
      using perm_switch_aux_h apply blast
    by simp

  lemma perm_aux_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> x \<otimes> y = x \<Longrightarrow> perm (x @ (y \<ominus> x)) y"
    apply (cut_tac x=x and y=y in perm_switch_aux_f)
    by (simp_all)
      lemma ZZZ_a: "x \<oplus> (y \<ominus> x) = (x \<oplus> y)"
        apply (simp add: addvars_def)
        by (induction y, simp_all)

      lemma ZZZ_b: "set (y \<otimes> z) \<inter> set x = {} \<Longrightarrow> (x \<ominus> (y \<ominus> z) \<ominus> (z \<ominus> y)) = (x \<ominus> y \<ominus> z)"
        by (induction x, simp_all add: set_diff set_inter)

      lemma subst_subst: "\<And> y z . a \<in> set z \<Longrightarrow> distinct x \<Longrightarrow> length x = length y \<Longrightarrow> length z = length x 
        \<Longrightarrow> subst x y (subst z x a) = subst z y a"
        apply (induction x, simp_all)
        apply (case_tac y, simp_all)
        apply (case_tac z, simp_all, auto)
        by (simp add: subst_in_set)

        
      lemma Subst_Subst_a: "set u \<subseteq> set z \<Longrightarrow> distinct x \<Longrightarrow> length x = length y \<Longrightarrow> length z = length x 
      \<Longrightarrow> Subst x y (Subst z x u) = (Subst z y u)"
        apply (induction u, simp_all)
        apply (case_tac y, simp_all)
        by (rule subst_subst,simp_all)
      lemma subst_in: "\<And> x' . length x = length x' \<Longrightarrow> a \<in> set x \<Longrightarrow> subst (x @ y) (x' @ y') a = subst x x' a"
        apply (induction x, simp_all)
        by (case_tac x', auto)

      lemma subst_switch: "\<And> x' . set x \<inter> set y = {} \<Longrightarrow> length x = length x' \<Longrightarrow> length y = length y' 
        \<Longrightarrow> subst (x @ y) (x' @ y') a = subst (y @ x) (y' @ x') a"
        apply (induction x, simp_all)
        apply (case_tac x', simp_all, safe)
        apply (simp add: subst_not_in_b)
        apply (case_tac "a \<in> set y", simp_all)
        apply (simp add: subst_in)
        by (simp add: subst_not_in_b)

      lemma Subst_switch: "set x \<inter> set y = {} \<Longrightarrow> length x = length x' \<Longrightarrow> length y = length y' 
        \<Longrightarrow> Subst (x @ y) (x'@ y') z = Subst (y @ x) (y'@ x') z"
        apply (induction z, simp_all)
        by (subst subst_switch, simp_all)

      lemma subst_comp: "\<And> x' . set x \<inter> set y = {} \<Longrightarrow> set x' \<inter> set y = {} \<Longrightarrow> length x = length x' 
        \<Longrightarrow> length y = length y' \<Longrightarrow> subst (x @ y) (x' @ y') a = subst y y' (subst x x' a)"
        apply (induction x, simp_all)
        by (case_tac x', simp_all)

      lemma Subst_comp: "set x \<inter> set y = {} \<Longrightarrow> set x' \<inter> set y = {} \<Longrightarrow> length x = length x' 
      \<Longrightarrow> length y = length y' \<Longrightarrow> Subst (x @ y) (x' @ y') z = Subst y y' (Subst x x' z)"
        by (induction z, simp_all add: subst_comp)

      lemma set_subst: "\<And> u' . length u = length u' \<Longrightarrow> subst u u' a \<in> set u' \<union> ({a} - set u)"
        apply (induction u, simp_all)
        by (case_tac u', simp_all, auto)


      lemma set_Subst_a: "length u = length u' \<Longrightarrow> set (Subst u u' z) \<subseteq> set u' \<union> (set z - set u)"
        apply (induction z, simp_all)
        by (cut_tac u = u and u' = u' and a  = a in set_subst, simp_all, auto)


      lemma set_SubstI: "length u = length u' \<Longrightarrow> set u' \<union> (set z - set u) \<subseteq> X \<Longrightarrow> set (Subst u u' z) \<subseteq> X"
        apply (rule_tac y = "set u' \<union> (set z - set u)" in order_trans)
        by (rule set_Subst_a, simp_all)

  lemma not_in_set_diff: "a \<notin> set x \<Longrightarrow> x \<ominus> ys @ a # zs = x \<ominus> ys @ zs"
    by (induction x, auto)
      
  lemma [simp]: "(X \<inter> (Y \<union> Z) = {}) = (X \<inter> Y = {} \<and> X \<inter> Z = {})"
    by auto
      
      (*very specialized*)  
      lemma Comp_assoc_new_subst_aux: "set u \<inter> set y \<inter> set z = {} \<Longrightarrow> distinct z \<Longrightarrow> length u = length u' 
        \<Longrightarrow> Subst (z \<ominus> v) (Subst u u' (z \<ominus> v)) z = Subst (u \<ominus> y \<ominus> v) (Subst u u' (u \<ominus> y \<ominus> v)) z"
        apply (induction z, simp_all, auto)
        apply (subst subst_notin)
        apply (simp_all add: set_diff)
        apply (case_tac "a \<in> set u", simp_all)
        apply (cut_tac z = "[a]" in Subst_Subst [of u u' _ "(u \<ominus> y \<ominus> v)"], simp_all)
        by (simp_all add: set_diff)

      lemma [simp]: "(x \<ominus> y \<ominus> (y \<ominus> z)) = (x \<ominus> y)"
        by (induction x, simp_all, auto simp add: set_diff)

      lemma [simp]: "(x \<ominus> y \<ominus> (y \<ominus> z \<ominus> z')) = (x \<ominus> y)"
        by (induction x, simp_all, auto simp add: set_diff)

      lemma diff_addvars: "x \<ominus> (y \<oplus> z) = (x \<ominus> y \<ominus> z)"
        by (induction x, auto simp add: set_diff set_addvars)

      lemma diff_redundant_a: "x \<ominus> y \<ominus> z \<ominus> (y \<ominus> u) = (x \<ominus> y \<ominus> z)"
        by (induction x, simp_all add: set_diff)

      lemma diff_redundant_b: "x \<ominus> y \<ominus> z \<ominus> (z \<ominus> u) = (x \<ominus> y \<ominus> z)"
        by (induction x, simp_all add: set_diff)

      lemma diff_redundant_c: "x \<ominus> y \<ominus> z \<ominus> (y \<ominus> u \<ominus> v) = (x \<ominus> y \<ominus> z)"
        by (induction x, simp_all add: set_diff)

      lemma diff_redundant_d: "x \<ominus> y \<ominus> z \<ominus> (z \<ominus> u \<ominus> v) = (x \<ominus> y \<ominus> z)"
        by (induction x, simp_all add: set_diff)

   lemma set_list_empty: "set x = {} \<Longrightarrow> x = []"
      by (induction x, simp_all)

    lemma [simp]: "(x \<ominus> x \<otimes> y) \<otimes> (y \<ominus> x \<otimes> y) = []"
      apply (rule set_list_empty)
      by (simp add: set_inter set_diff, auto)

    lemma [simp]: "set x \<inter> set (y \<ominus> x) = {}"
      by (simp add: set_diff)

lemma [simp]:" distinct x \<Longrightarrow> distinct y \<Longrightarrow> set x \<subseteq> set y \<Longrightarrow> perm (x @ (y \<ominus> x)) y"
  by (metis append_Nil diff_subset perm_switch)

    lemma [simp]: "perm x y \<Longrightarrow> set x \<subseteq> set y"
      by (simp add: perm_set_eq)
    lemma [simp]: "perm x y \<Longrightarrow> set y \<subseteq> set x"
      by (simp add: perm_set_eq)

    lemma [simp]: "set (x \<ominus> y) \<subseteq> set x"
      by (auto simp add: set_diff)
        
      lemma perm_diff[simp]: "\<And> x' . perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x \<ominus> y) (x' \<ominus> y')"
        apply (induction x, simp_all)
        apply (frule_tac x = y and y = y' in perm_set_eq, simp)
        apply (simp add: split_perm union_diff)
        apply auto
        apply (simp_all add: union_diff)
        apply (metis union_diff)
        by (metis union_diff)

    lemma [simp]: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x @ y) (x' @ y')"
      by (simp add: perm_mset)

    lemma [simp]: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x \<oplus> y) (x' \<oplus> y')"
      by (simp add: addvars_def)

    thm distinct_diff
      
declare distinct_diff [simp]
  (*
    declare perm_set_eq [simp]
*)
    lemma [simp]: "\<And> x' . perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x \<otimes> y) (x' \<otimes> y')"
      apply (induction x, simp_all, safe)
      apply (simp add: split_perm, safe, simp_all)
      apply (rule_tac x = "ya \<otimes> y'" in exI)
      apply (rule_tac x = "y'a \<otimes> y'" in exI)
      apply (simp add: append_inter)
      apply (subgoal_tac "perm (x \<otimes> y) ((ya @ y'a) \<otimes> y')")
      apply (subst (asm) append_inter, simp_all add: perm_set_eq)

      apply (simp add: split_perm, safe, simp_all)
      apply (subgoal_tac "perm (x \<otimes> y) ((ya @ y'a) \<otimes> y')")
      apply (subst (asm) append_inter, simp add: append_inter)
      by simp

    declare distinct_inter [simp]

    lemma perm_ops: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      apply safe
      by (simp_all)
      

    lemma [simp]: "perm x' x \<Longrightarrow> perm y' y \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      by (rule_tac x = x and y = y and x' = x' and y' = y' in perm_ops, unfold perm_mset, simp_all)
      
    lemma [simp]: "perm x x' \<Longrightarrow> perm y' y \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      by (rule_tac x = x and y = y and x' = x' and y' = y' in perm_ops, unfold perm_mset, simp_all)

    lemma [simp]: "perm x' x \<Longrightarrow> perm y y' \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      by (rule_tac x = x and y = y and x' = x' and y' = y' in perm_ops, unfold perm_mset, simp_all)

      lemma diff_cons: "(x \<ominus> (a # y)) = (x \<ominus> [a] \<ominus> y)"
        by (induction x, simp_all)

    lemma [simp]: "x \<oplus> y \<oplus> x = x \<oplus> y"
        apply (simp add: addvars_def)
        by (simp add: diff_eq diff_union)

      lemma  subst_subst_inv: "\<And> y . distinct y \<Longrightarrow> length x = length y \<Longrightarrow> a \<in> set x \<Longrightarrow> subst y x (subst x y a) = a"
        by (induction x, auto)
              

      lemma Subst_Subst_inv: "distinct y \<Longrightarrow> length x = length y \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> Subst y x (Subst x y z) = z"
        apply (induction z)
        by (simp_all add: subst_subst_inv)

      (*move*)
      lemma perm_append: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x @ y) (x' @ y')"
        by (simp add: perm_mset)



      lemma "x' = y @ a # y' \<Longrightarrow> perm x (y @ y') \<Longrightarrow> perm (a # x) x'"
        by (simp add: perm_mset)



      lemma perm_diff_eq: "perm y y' \<Longrightarrow> (x \<ominus> y) = (x \<ominus> y')"
        apply (drule perm_set_eq)
        by (induction x, auto)

      lemma [simp]: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False"
        by auto
      lemma [simp]: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
        by auto

      lemma [simp]: "B \<inter> A = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
        by auto
      lemma [simp]: "B \<inter> A = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False"
        by auto

lemma distinct_perm_set_eq: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm x y = (set x = set y)"
  by (simp add: perm_mset set_eq_iff_mset_eq_distinct)

      lemma set_perm: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set x = set y \<Longrightarrow> perm x y"
        by (simp add: distinct_perm_set_eq)

      lemma distinct_perm_switch: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm (x \<oplus> y) (y \<oplus> x)"
        apply (simp add: addvars_def)
        by (rule set_perm, simp_all add: set_diff, auto)
lemma listinter_diff: "(x \<otimes> y) \<ominus> z = (x \<ominus> z) \<otimes> (y \<ominus> z)"
  apply (induction x, simp_all)
  by (simp add: set_diff)
    
lemma set_listinter: "set y = set z \<Longrightarrow> x \<otimes> y = x \<otimes> z"
  by (induction x, simp_all)
    
lemma AAA_c: "a \<notin> set x \<Longrightarrow> x \<ominus> [a] = x"
  by (induction x, simp_all, auto)

lemma distinct_perm_cons: "distinct x \<Longrightarrow> perm (a # y) x \<Longrightarrow> perm y (x \<ominus> [a])"
  apply (rule set_perm)
    apply (meson dist_perm distinct.simps(2) perm_sym)
   apply simp
  proof -
    assume a1: "distinct x"
  assume a2: "perm (a # y) x"
  then have "set (a # y) = set x"
    by (meson perm_set_eq)
  then show "set y = set (x \<ominus> [a])"
    using a2 a1 by (metis (no_types) AAA_c diff.simps(2) dist_perm distinct.simps(2) list.set_intros(1) perm_sym set_diff)
qed
   
lemma listinter_empty[simp]: " y \<otimes> [] = []"
  by (induction y, simp_all)
    

lemma subsetset_inter: "set x \<subseteq> set y \<Longrightarrow> (x \<otimes> y) = x"
  by (induction x, auto)

  
lemma addvars_addsame: "x \<oplus> y \<oplus> (x \<ominus> z) = x \<oplus> y"
  by (metis ListProp.diff_eq ZZZ_a addvars_empty diff_addvars)

lemma ZZZ: "x \<ominus> x \<oplus> y = []"
  by (simp add: ListProp.diff_eq diff_addvars)

lemma perm_dist_mem: "distinct x \<Longrightarrow> a \<in> set x \<Longrightarrow> perm (a # (x \<ominus> [a])) x"
  by (metis Diff_iff distinct.simps(2) distinct_diff empty_set insert_Diff list.set(2) list.set_intros(1) set_diff set_perm) 


lemma addvars_diff: "b # (x \<oplus> (z \<ominus> [b])) = (b # x) \<oplus> z"
proof -
  have "z \<ominus> [b] \<ominus> b # x = z \<ominus> [b] \<ominus> [] \<ominus> [b] \<ominus> x \<ominus> []"
    by (metis diff_cons diff_emptyset)
    then have f1: "x @ (z \<ominus> [b] \<ominus> b # x) = x \<oplus> (z \<ominus> [b] \<ominus> b # x)"
      by (metis (no_types) ZZZ_a addvars_def diff_cons)
    have "z \<ominus> [b] \<ominus> b # x = z \<ominus> [b] \<ominus> x \<ominus> [b]"
      by (metis (no_types) diff_cons diff_sym)
    then show ?thesis
      using f1 by (metis (no_types) addvars_def append.simps(2) diff_cons)
  qed

    
lemma perm_cons: "a \<in> set y \<Longrightarrow> distinct y \<Longrightarrow> perm x (y \<ominus> [a]) \<Longrightarrow> perm (a # x) y"
  apply (rule set_perm, simp_all add: set_diff perm_set_eq, safe)
  using dist_perm distinct_diff perm_sym by blast
 
end