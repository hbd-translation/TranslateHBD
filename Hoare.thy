theory Hoare imports Refinement
begin
   definition "if_stm p S T = ([.p.] o S) \<sqinter> ([.-p.] o T)"
   definition "while_stm p S = lfp (\<lambda> X . if_stm p (S o X) Skip)"
   definition "Hoare p S q = (p \<le> S q)"
   
   definition "Sup_less x (w::'b::wellorder) = Sup {y ::'a::complete_lattice . \<exists> v < w . y = x v}"

  lemma Sup_less_upper:
    "v < w \<Longrightarrow> P v \<le> Sup_less P w"
    by (simp add: Sup_less_def, rule Sup_upper, blast)

  lemma Sup_less_least:
    "(!! v . v < w \<Longrightarrow> P v \<le> Q) \<Longrightarrow> Sup_less P w \<le> Q"
    by (simp add: Sup_less_def, rule Sup_least, blast)

  theorem fp_wf_induction:
    "f x  = x \<Longrightarrow> mono f \<Longrightarrow> (\<forall> w . (y w) \<le> f (Sup_less y w)) \<Longrightarrow> Sup (range y) \<le> x"
    apply (rule Sup_least)
    apply (simp add: image_def, safe, simp)
    apply (rule less_induct, simp_all)
    apply (rule_tac y = "f (Sup_less y xa)" in order_trans, simp)
    apply (drule_tac x = "Sup_less y xa" and y = "x" in monoD)
    by (simp add: Sup_less_least, auto)

  theorem lfp_wf_induction: "mono f \<Longrightarrow> (\<forall> w . (p w) \<le> f (Sup_less p w)) \<Longrightarrow> Sup (range p) \<le> lfp f"
    apply (rule fp_wf_induction, simp_all)
    by (drule lfp_unfold, simp)
 
  theorem lfp_wf_induction_a: "mono f \<Longrightarrow> (\<forall> w . (p w) \<le> f (Sup_less p w)) \<Longrightarrow> (SUP a. p a) \<le> lfp f"
    apply (rule fp_wf_induction, simp_all)
    by (drule lfp_unfold, simp)

   definition  "mono_mono F = (mono F \<and> (\<forall> f . mono f \<longrightarrow> mono (F f)))"
  
   
  definition "post_fun (p::'a::order) q = (if p \<le> q then \<top> else \<bottom>)"

  lemma post_mono [simp]: "mono (post_fun p :: (_::{order_bot,order_top}))"
     apply (simp add: post_fun_def  mono_def, safe)
     apply (subgoal_tac "p \<le> y", simp)
     by (rule_tac y = x in order_trans, simp_all)

  lemma post_refin [simp]: "mono S \<Longrightarrow> ((S p)::'a::bounded_lattice) \<sqinter> (post_fun p) x \<le> S x"
    apply (simp add: le_fun_def post_fun_def, safe)
    by (rule_tac f = S in monoD, simp_all)

  lemma post_top [simp]: "post_fun p p = \<top>"
    by (simp add: post_fun_def)
 
  theorem hoare_refinement_post:
    "mono f \<Longrightarrow>  (Hoare x  f y) = ({.x::'a::boolean_algebra.} o (post_fun y) \<le> f)"
    apply safe
    apply (simp_all add: Hoare_def)
    apply (simp_all add: le_fun_def)
    apply (simp add: assert_def, safe)
    apply (rule_tac y = "f y \<sqinter> post_fun y xa" in order_trans, simp_all)
    apply (rule_tac y = "x" in order_trans, simp_all)
    apply (simp add: assert_def)
    by (drule_tac x = "y" in spec,simp)
  
  lemma assert_Sup_range: "{.Sup (range (p::'W \<Rightarrow> 'a::complete_distrib_lattice)).} = Sup(range (assert o p))"
    by (simp add: fun_eq_iff assert_def SUP_inf)

  lemma Sup_range_comp: "(Sup (range p)) o S = Sup (range (\<lambda> w . ((p w) o S)))"
    by (simp add: fun_eq_iff)
  
  theorem lfp_mono [simp]:
    "mono_mono F \<Longrightarrow> mono (lfp F)"
    apply (simp add: mono_mono_def)
    apply (rule_tac f="F" and P = "mono" in lfp_ordinal_induct)
    apply (simp_all add: mono_def)
    apply (intro allI impI SUP_least)
    apply (rule_tac y = "f y" in order_trans)
    apply (auto intro: SUP_upper)
    done
 
  lemma Sup_less_comp: "(Sup_less P) w o S = Sup_less (\<lambda> w . ((P w) o S)) w"
    apply (simp add: Sup_less_def fun_eq_iff, safe)
    apply (subgoal_tac "((\<lambda>f. f (S x)) ` {y. \<exists>v<w. \<forall>x. y x = P v x}) = ((\<lambda>f. f x) ` {y. \<exists>v<w. \<forall>x. y x = P v (S x)})")
      
      apply presburger
    by (auto)

  lemma assert_Sup: "{.Sup (X::'a::complete_distrib_lattice set).} = Sup (assert ` X)"
    by (simp add: fun_eq_iff assert_def Sup_inf)

  lemma Sup_less_assert: "Sup_less (\<lambda>w. {. (p w)::'a::complete_distrib_lattice .}) w = {.Sup_less p w.}"
    apply (simp add: Sup_less_def assert_Sup image_def)
    proof -
      have "{{. a .} |a. \<exists>b<w. a = p b} = {f. \<exists>b<w. f = {. p b .}}"
        by auto
      then show "Sup {f. \<exists>b<w. f = {. p b .}} = (SUP a:{a. \<exists>b<w. a = p b}. {. a .})"
        by (metis setcompr_eq_image)
    qed
 
  theorem hoare_fixpoint:
    "mono_mono F \<Longrightarrow> 
       (\<forall> f w . mono f \<longrightarrow> (Hoare (Sup_less p w) f y \<longrightarrow> Hoare ((p w)::'a \<Rightarrow> bool) (F f) y)) \<Longrightarrow> Hoare(Sup (range p)) (lfp F) y"
    apply (simp add: mono_mono_def hoare_refinement_post assert_Sup_range Sup_range_comp del: )
    apply (rule lfp_wf_induction)
    apply auto
    apply (simp add: Sup_less_comp [THEN sym])
    apply (simp add: Sup_less_assert)
    apply (drule_tac x = "{. Sup_less p w .} \<circ> post_fun y" in spec, safe)
    apply simp_all
    apply (drule_tac x = "w" in spec, safe)
    by (simp add: le_fun_def)

  lemma if_mono[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (if_stm b S T)"
    by (simp add: if_stm_def)
    

  lemma [simp]: "mono x \<Longrightarrow> mono_mono (\<lambda>X . if_stm b (x \<circ> X) Skip)"
    apply (simp add: mono_mono_def)
    apply (simp add: mono_def, safe)
    apply (simp add: if_stm_def assume_def, auto)
    apply (metis le_fun_def predicate1D)
    by (metis le_fun_def predicate1D)
    
  theorem hoare_sequential:
    "mono S \<Longrightarrow> (Hoare p (S o T) r) = ( (\<exists> q. Hoare p S q \<and> Hoare q T r))"
    by (metis (no_types) Hoare_def monoD o_def order_refl order_trans)

  theorem hoare_choice:
    "Hoare  p (S \<sqinter> T) q = (Hoare p S q \<and> Hoare p T q)"
    by (simp_all add: Hoare_def inf_fun_def)

  theorem hoare_assume:
    "(Hoare P [.R.] Q) = (P \<sqinter> R \<le> Q)"
    apply (simp add: Hoare_def assume_def)
    apply safe
    apply (case_tac "(inf P R) \<le> (inf (sup (- R) Q) R)")
    apply (simp add: inf_sup_distrib2)
    apply (simp add: le_infI1)
    apply (case_tac "(sup (-R) (inf P R)) \<le> sup (- R) Q")
    apply (simp add: sup_inf_distrib1)
    by (simp add: le_supI2) 

  lemma hoare_if: "mono S \<Longrightarrow> mono T \<Longrightarrow> Hoare (p \<sqinter> b) S q \<Longrightarrow> Hoare (p \<sqinter> -b) T q \<Longrightarrow> Hoare p (if_stm b S T) q"
    apply (simp add: if_stm_def)
    apply (simp add: hoare_choice, safe)
    apply (simp_all add:  hoare_sequential)
    apply (rule_tac x = " (p \<sqinter> b)" in exI, simp)
    apply (simp add: hoare_assume) 
    apply (rule_tac x = " (p \<sqinter> -b)" in exI, simp)
    by (simp add: hoare_assume)

  lemma hoare_while:
      "mono x \<Longrightarrow> (\<forall> w . Hoare ((p w) \<sqinter> b) x (Sup_less p w)) \<Longrightarrow>  Hoare  (Sup (range p)) (while_stm b x) ((Sup (range p)) \<sqinter> -b)"
    apply (cut_tac y = " ((SUP x. p x) \<sqinter> - b)" and p = p and F = "\<lambda> X . if_stm b (x o X) Skip" in hoare_fixpoint, simp_all)
    apply safe
    apply (rule hoare_if, simp_all)
    apply (simp_all add:  hoare_sequential)
    apply (rule_tac x = " (Sup_less p w)" in exI, simp_all)
    apply (simp add: Hoare_def Skip_def, auto)
    by (simp add: while_stm_def)

  lemma hoare_prec_post: "mono S \<Longrightarrow> p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> Hoare p' S q' \<Longrightarrow> Hoare p S q"
    apply (simp add: Hoare_def)
    apply (rule_tac y = p' in order_trans, simp_all)
    apply (rule_tac y = "S q'" in order_trans, simp_all)
    using monoD by auto

  lemma [simp]: "mono x \<Longrightarrow>  mono (while_stm b x)"
    by (simp add: while_stm_def)

  lemma hoare_while_a:
    "mono x \<Longrightarrow> (\<forall> w . Hoare ((p w) \<sqinter> b) x (Sup_less p w)) \<Longrightarrow> p' \<le>  (Sup (range p)) \<Longrightarrow> ((Sup (range p)) \<sqinter> -b) \<le> q 
      \<Longrightarrow>  Hoare p' (while_stm b x) q"
    apply (rule hoare_prec_post, simp_all)
    by (drule hoare_while, simp_all)

  lemma hoare_update: "p \<le> q o f \<Longrightarrow> Hoare p [-f-] q"
    by (simp add: Hoare_def update_def demonic_def le_fun_def)

  lemma hoare_demonic: "(\<And> x y . p x \<Longrightarrow> r x y \<Longrightarrow> q y) \<Longrightarrow> Hoare p [:r:] q"
    by (simp add: Hoare_def demonic_def le_fun_def)

end