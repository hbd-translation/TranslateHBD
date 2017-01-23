theory Constructive imports Main
begin
  section{*Constructive Functions*}

  notation
    bot ("\<bottom>") and
    top ("\<top>") and
    inf (infixl "\<sqinter>" 70)
    and sup (infixl "\<squnion>" 65)

  class order_bot_max = order_bot +
    fixes maximal :: "'a \<Rightarrow> bool"
    assumes maximal_def: "maximal x = (\<forall> y . \<not> x < y)"
    assumes [simp]: "\<not> maximal \<bottom>"
    begin
      lemma ex_not_le_bot[simp]: "\<exists> a. \<not> a \<le> \<bottom>"
        apply (subgoal_tac "\<not> maximal \<bottom>")
        apply (subst (asm) maximal_def, simp_all add: less_le, auto)
        apply (rule_tac x = x in exI, auto)
        apply (subgoal_tac "x = \<bottom>", simp)
        by (rule antisym, simp_all)
    end

  instantiation "option" :: (type) order_bot_max
    begin
      definition bot_option_def: "(\<bottom>::'a option) = None"
      definition le_option_def: "((x::'a option) \<le> y) = (x = None \<or> x = y)"
      definition less_option_def: "((x::'a option) < y) = (x \<le> y \<and> \<not> (y \<le> x))"
      definition maximal_option_def: "maximal (x::'a option) = (\<forall> y . \<not> x < y)"

      instance 
      proof
        qed (auto simp add: le_option_def less_option_def maximal_option_def bot_option_def)

     lemma [simp]: "None \<le> x"
      by (subst bot_option_def [THEN sym], simp)
    end

  context order_bot
    begin
      definition "is_lfp f x = ((f x = x) \<and> (\<forall> y . f y = y \<longrightarrow> x \<le> y))"
      definition "emono f = (\<forall> x y. x \<le> y \<longrightarrow> f x \<le> f y)"

      definition "Lfp f = Eps (is_lfp f)"

      lemma lfp_unique: "is_lfp f x \<Longrightarrow> is_lfp f y \<Longrightarrow> x = y"
        apply (simp add: is_lfp_def)
        by (simp add: local.antisym)

      lemma lfp_exists: "is_lfp f x \<Longrightarrow> Lfp f = x"
        apply (rule lfp_unique, simp_all)
        by (simp add: Lfp_def someI)
  
      lemma emono_a: "emono f \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
        by (simp add: emono_def)

      lemma emono_fix: "emono f \<Longrightarrow> f y = y \<Longrightarrow> (f ^^ n) \<bottom> \<le> y"
        apply (induction n)
        apply (simp_all)
        apply (drule emono_a, simp_all)
        by simp

      lemma emono_is_lfp: "emono (f::'a \<Rightarrow> 'a) \<Longrightarrow> (f ^^ (n + 1)) \<bottom> = (f ^^ n) \<bottom> \<Longrightarrow> is_lfp f ((f ^^ n) \<bottom>)"
        apply (simp add: is_lfp_def, safe)
        by (rule emono_fix, simp_all)

      lemma emono_lfp_bot: "emono (f::'a \<Rightarrow> 'a) \<Longrightarrow> (f ^^ (n + 1)) \<bottom> = (f ^^ n) \<bottom> \<Longrightarrow> Lfp f = ((f ^^ n) \<bottom>)"
        apply (drule emono_is_lfp, simp_all)
        by (simp add: lfp_exists)


      lemma emono_up: "emono f \<Longrightarrow> (f ^^ n) \<bottom> \<le> (f ^^ (Suc n)) \<bottom>"
        apply (induction n)
        apply (simp_all)
        by (drule emono_a, simp_all)
    end

   context order
    begin
       definition "min_set A = (SOME n . n \<in> A \<and> (\<forall> x \<in> A . n \<le> x))"
    end

   lemma min_nonempty_nat_set_aux: "\<forall> A . (n::nat) \<in> A \<longrightarrow> (\<exists> k \<in> A . (\<forall> x \<in> A . k \<le> x))"
     apply (induction n, safe)
     apply (rule_tac x = 0 in bexI, simp_all)
     apply (case_tac "0 \<in> A")
     apply (rule_tac x = 0 in bexI, simp_all)
     apply (drule_tac x = "{n . Suc n \<in> A}" in spec)
     apply safe
     apply (rule_tac x = "Suc k" in bexI, simp_all, safe)
     apply (drule_tac x = "x - 1" in spec)
     by (case_tac x, simp_all)

   lemma min_nonempty_nat_set: "(n::nat) \<in> A \<Longrightarrow> (\<exists> k . k \<in> A \<and> (\<forall> x \<in> A . k \<le> x))"
     by (cut_tac min_nonempty_nat_set_aux, auto)

  thm someI_ex

  lemma min_set_nat_aux: "(n::nat) \<in> A \<Longrightarrow> min_set A \<in> A \<and> (\<forall> x \<in> A . min_set A \<le> x)"
    apply (simp add: min_set_def)
    apply (drule min_nonempty_nat_set)
    by (rule someI_ex, simp_all)

  lemma "(n::nat) \<in> A \<Longrightarrow> min_set A \<in> A \<and> min_set A \<le> n"
    by (simp add: min_set_nat_aux)
    
  lemma min_set_in: "(n::nat) \<in> A \<Longrightarrow> min_set A \<in> A"
    by (simp add: min_set_nat_aux)

  lemma min_set_less: "(n::nat) \<in> A \<Longrightarrow> min_set A \<le> n"
    by (simp add: min_set_nat_aux)


  definition "mono_a f = (\<forall> a b a' b'. (a::'a::order) \<le> a' \<and> (b::'b::order) \<le> b' \<longrightarrow> f a b \<le> f a' b')"

  class fin_cpo = order_bot_max +
    
    assumes fin_up_chain: "(\<forall> i:: nat . a i \<le> a (Suc i)) \<Longrightarrow> \<exists> n . \<forall> i \<ge> n . a i = a n"
    begin
      lemma emono_ex_lfp: "emono f \<Longrightarrow> \<exists> n . is_lfp f ((f ^^ n) \<bottom>)"
        apply (cut_tac a = "\<lambda> i . (f ^^ i) \<bottom>" in fin_up_chain)
        apply (safe, rule emono_up, simp)
        apply (rule_tac x= n in exI)
        apply (rule emono_is_lfp, simp)
        by (drule_tac x = "n + 1" in spec, simp)

      lemma emono_lfp: "emono f \<Longrightarrow> \<exists> n . Lfp f = (f ^^ n) \<bottom>"
        apply (drule emono_ex_lfp, safe)
        apply (rule_tac x = n in exI)
        by (rule lfp_exists, simp)

      lemma emono_is_lfp: "emono f \<Longrightarrow> is_lfp f (Lfp f)"
        apply (drule emono_ex_lfp, safe)
        by (frule lfp_exists, simp)

      definition "lfp_index (f::'a \<Rightarrow> 'a) = min_set {n . (f ^^ n) \<bottom> = (f ^^ (n + 1)) \<bottom>}"

      lemma lfp_index_aux: "emono f \<Longrightarrow> (\<forall> i < (lfp_index f) . (f ^^ i) \<bottom> < (f ^^ (i + 1)) \<bottom>) \<and> (f ^^ (lfp_index f)) \<bottom> = (f ^^ ((lfp_index f) + 1)) \<bottom>"
        apply (simp add: lfp_index_def)
        apply safe
        apply (simp add: less_le_not_le, safe)
        apply (cut_tac n = i in emono_up, simp_all)
        apply (cut_tac n = i and A = "{n . (f ^^ n) \<bottom> = (f ^^ (n + 1)) \<bottom>}" in min_set_less, simp)
        apply (rule antisym, simp_all)
        apply (cut_tac n = i in emono_up, simp_all)
        apply (cut_tac a = "\<lambda> i . (f ^^ i) \<bottom>" in fin_up_chain, simp, safe)
        apply (drule emono_up, simp)
        apply (cut_tac n = "n" and A = "{n . (f ^^ n) \<bottom> = (f ^^ (n + 1)) \<bottom>}" in min_set_in)
        apply (drule_tac x = "Suc n" in spec, simp)
        by simp

      lemma [simp]: "emono f \<Longrightarrow> i < lfp_index f \<Longrightarrow> (f ^^ i) \<bottom> < f ((f ^^ i) \<bottom>)"
        by (drule lfp_index_aux, simp)

      lemma [simp]: "emono f \<Longrightarrow> f ((f ^^ (lfp_index f)) \<bottom>) = (f ^^ (lfp_index f)) \<bottom>"
        by (drule lfp_index_aux, simp)

      lemma "emono f \<Longrightarrow> Lfp f = (f ^^ lfp_index f) \<bottom>"
        by (rule emono_lfp_bot, simp_all)



      lemma AA_aux: "emono f \<Longrightarrow> (\<And> b . b \<le> a \<Longrightarrow> f b \<le> a) \<Longrightarrow> (f ^^ n) \<bottom> \<le> a"
        by (induction n, simp_all)

      lemma AA: "emono f \<Longrightarrow> (\<And> b . b \<le> a \<Longrightarrow> f b \<le> a) \<Longrightarrow> Lfp f \<le> a"
        apply (cut_tac f = f in  emono_lfp, simp_all, safe, simp)
        by (simp add: AA_aux)

      lemma BB: "emono f \<Longrightarrow> f (Lfp f) = Lfp f"
        using local.emono_is_lfp local.is_lfp_def by blast
 
      lemma Lfp_mono: "emono f \<Longrightarrow> emono g \<Longrightarrow> (\<And> a . f a \<le> g a) \<Longrightarrow> Lfp f \<le> Lfp g"
        by (metis AA BB local.emono_def local.order_trans)


    end
    declare [[show_types]]

      lemma [simp]: "mono_a f \<Longrightarrow> emono (f a)"
        by (simp add: emono_def mono_a_def)

      lemma [simp]: "mono_a f \<Longrightarrow> emono (\<lambda> a . f a b)"
        by (simp add: emono_def mono_a_def)

      lemma mono_aD: "mono_a f \<Longrightarrow> a \<le> a' \<Longrightarrow> b \<le> b' \<Longrightarrow> f a b \<le> f a' b'"
        by (simp add: mono_a_def)

      lemma [simp]: "mono_a (f::'a::fin_cpo \<Rightarrow> 'b::fin_cpo \<Rightarrow> 'b) \<Longrightarrow> mono_a g \<Longrightarrow> emono (\<lambda>b. f (Lfp (g b)) b)"
        apply (simp add: emono_def, safe)
        apply (rule_tac f = f in mono_aD, simp_all)
        by (rule Lfp_mono, simp_all add: mono_a_def)

      lemma CCC: "mono_a  (f::'a::fin_cpo \<Rightarrow> 'b::fin_cpo \<Rightarrow> 'b) \<Longrightarrow> mono_a g \<Longrightarrow> Lfp (\<lambda>a. g (Lfp (f a)) a) \<le> Lfp (g (Lfp (\<lambda>b. f (Lfp (g b)) b)))"
        apply (rule AA, simp_all)
        apply (subst (2) BB [THEN sym], simp_all)
        apply (rule_tac f = g in mono_aD, simp_all)
        apply (rule AA, simp_all)
        apply (subst BB [THEN sym], simp_all)
        by (rule_tac f = f in mono_aD, simp_all)


    lemma Lfp_commute: "mono_a (f::'a::fin_cpo \<Rightarrow> 'b::fin_cpo \<Rightarrow> 'b::fin_cpo) \<Longrightarrow> mono_a g \<Longrightarrow> Lfp (\<lambda> b . f  (Lfp (\<lambda> a . (g (Lfp (f a))) a)) b) = Lfp (\<lambda> b . f (Lfp (g b)) b)"
      apply (rule antisym)
      apply (rule AA, simp_all)
      apply (subst (3) BB [THEN sym], simp_all)
      apply (rule_tac f = f in mono_aD)
      apply simp_all
      by (simp_all add: CCC)

  instantiation "option" :: (type) fin_cpo
    begin
      lemma fin_up_non_bot: "(\<forall> i . (a::nat \<Rightarrow> 'a option) i \<le> a (Suc i)) \<Longrightarrow> a n \<noteq> \<bottom> \<Longrightarrow> n \<le> i \<Longrightarrow> a i = a n"
        apply (induction i, simp_all)
        apply (case_tac "n \<le> i", simp_all)
        apply (drule_tac x = i in spec)
        apply (simp add: le_option_def bot_option_def, safe, simp_all)
        using le_Suc_eq by blast

     lemma fin_up_chain_option: "(\<forall> i:: nat . (a::nat \<Rightarrow> 'a option) i \<le> a (Suc i)) \<Longrightarrow> \<exists> n . \<forall> i \<ge> n . a i = a n"
      apply (case_tac "\<exists> n .  a n \<noteq> \<bottom>", safe, simp_all)
      apply (rule_tac x = n in exI, safe)
      by (rule fin_up_non_bot, simp_all)
      
    instance
      proof
        qed (simp add: fin_up_chain_option)
    end

  instantiation "prod" :: (order_bot_max, order_bot_max) order_bot_max
    begin
      definition bot_prod_def: "(\<bottom> :: 'a \<times> 'b) = (\<bottom>, \<bottom>)"
      definition le_prod_def: "(x \<le> y) = (fst x \<le> fst y \<and> snd x \<le> snd y)"
      definition less_prod_def: "((x::'a\<times>'b) < y) = (x \<le> y \<and> \<not> (y \<le> x))"
      definition maximal_prod_def: "maximal (x::'a \<times> 'b) = (\<forall> y . \<not> x < y)"

      instance proof
        qed (auto simp add: le_prod_def less_prod_def bot_prod_def maximal_prod_def)
    end

  instantiation "prod" :: (fin_cpo, fin_cpo) fin_cpo
    begin
      
      lemma fin_up_chain_prod: "(\<forall> i:: nat . (a::nat \<Rightarrow> 'a \<times> 'b) i \<le> a (Suc i)) \<Longrightarrow> \<exists> n . \<forall> i \<ge> n . a i = a n"
        apply (cut_tac a = "fst o a" in fin_up_chain)
        apply (simp add: le_prod_def)
        apply (cut_tac a = "snd o a" in fin_up_chain)
        apply (simp add: le_prod_def)
        apply safe
        apply (rule_tac x = "max n na" in exI)
        by (metis (no_types, hide_lams) comp_apply max.bounded_iff max.cobounded1 max.cobounded2 prod.collapse)
      instance proof
        qed (auto simp add: fin_up_chain_prod)
    end

end
