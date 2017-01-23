theory Refinement imports Main
begin
  section{*Monotonic Predicate Transformers. Refinement Calculus.*}
 
  notation
    bot ("\<bottom>") and
    top ("\<top>") and
    inf (infixl "\<sqinter>" 70)
    and sup (infixl "\<squnion>" 65)

  definition
    demonic :: "('a => 'b::lattice) => 'b => 'a \<Rightarrow> bool" ("[: _ :]" [0] 1000) where
    "[:Q:] p s = (Q s \<le> p)"

  definition
    assert::"'a::semilattice_inf => 'a => 'a" ("{. _ .}" [0] 1000) where
    "{.p.} q \<equiv>  p \<sqinter> q"

  definition
    "assume"::"('a::boolean_algebra) => 'a => 'a" ("[. _ .]" [0] 1000) where
    "[.p.] q \<equiv>  (-p \<squnion> q)"

  definition
    angelic :: "('a \<Rightarrow> 'b::{semilattice_inf,order_bot}) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("{: _ :}" [0] 1000) where
    "{:Q:} p s = (Q s \<sqinter> p \<noteq> \<bottom>)"


  syntax
    "_assert" :: "patterns => logic => logic"    ("(1{._._.})")
  translations
    "_assert x P" == "CONST assert (_abs x P)"

  term "{. x, z . P x y.}"

  syntax "_demonic" :: "patterns => patterns => logic => logic" ("([:_\<leadsto>_._:])")
  translations
    "_demonic x y t" == "(CONST demonic (_abs x (_abs y t)))"

  syntax "_angelic" :: "patterns => patterns => logic => logic" ("({:_ \<leadsto> _._:})")
  translations
    "_angelic x y t" == "(CONST angelic (_abs x (_abs y t)))"


  lemma assert_o_def: "{.f o g.} = {.(\<lambda> x . f (g x)).}"
    by (simp add: o_def)

  lemma demonic_demonic: "[:r:] o [:r':] = [:r OO r':]"
    by (simp add: fun_eq_iff le_fun_def demonic_def, auto)

  lemma assert_demonic_comp: "{.p.} o [:r:] o {.p'.} o [:r':] = 
      {.x . p x \<and> (\<forall> y . r x y \<longrightarrow> p' y).} o [:r OO r':]"
      by (auto simp add: fun_eq_iff le_fun_def assert_def demonic_def)

  lemma demonic_assert_comp: "[:r:] o {.p.} = {.x.(\<forall> y . r x y \<longrightarrow> p y).} o [:r:]"
      by (auto simp add: fun_eq_iff le_fun_def assert_def demonic_def)

  lemma assert_assert_comp: "{.p::'a::lattice.} o {.p'.} = {.p \<sqinter> p'.}"
      by (simp add: fun_eq_iff le_fun_def assert_def demonic_def inf_assoc)

  lemma assert_assert_comp_pred: "{.p.} o {.p'.} = {.x . p x \<and> p' x.}"
      by (simp add: fun_eq_iff le_fun_def assert_def demonic_def inf_assoc)
  
  definition "inpt r x = (\<exists> y . r x y)"

  definition "trs r = {. inpt r.} o [:r:]"


  lemma "trs (\<lambda> x y . x = y) q x = q x"
    by (simp add: trs_def fun_eq_iff assert_def demonic_def inpt_def bot_fun_def le_fun_def)

  lemma assert_demonic_prop: "{.p.} o [:r:] = {.p.} o [:(\<lambda> x y . p x) \<sqinter> r:]"
    by (auto simp add: fun_eq_iff assert_def demonic_def)

  lemma trs_trs: "(trs r) o (trs r') = trs ((\<lambda> s t. (\<forall> s' . r s s' \<longrightarrow> (inpt r' s'))) \<sqinter> (r OO r'))" (is "?S = ?T")
    proof -
      have [simp]: "(\<lambda>x. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y)) = inpt ((\<lambda>s t. \<forall>s'. r s s' \<longrightarrow> inpt r' s') \<sqinter> r OO r')"
        by (auto simp add: fun_eq_iff inpt_def relcompp_apply, blast)
      have [simp]: "(\<lambda>x y. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y)) \<sqinter> r OO r' = (\<lambda>s t. \<forall>s'. r s s' \<longrightarrow> inpt r' s') \<sqinter> r OO r'"
        by (auto simp add: fun_eq_iff inpt_def)
      have "?S = {. inpt r .} \<circ> [: r :] \<circ> {. inpt r' .} \<circ> [: r' :]"
        by (simp add: trs_def comp_assoc[symmetric])
      also have "... = {. \<lambda>x. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y) .} \<circ> [: r OO r' :]"
        by (simp add: assert_demonic_comp)
      also have "... =  {. \<lambda>x. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y) .} o [:(\<lambda> x y . inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y))  \<sqinter> (r OO r'):]"
        by (subst assert_demonic_prop, simp)
      also have "... = ?T"
        by (simp add: trs_def)
      finally show ?thesis by simp
    qed

  lemma assert_demonic_refinement: "({.p.} o [:r:] \<le> {.p'.} o [:r':]) = (p \<le> p' \<and> (\<forall> x . p x \<longrightarrow> r' x \<le> r x))"
    by  (auto simp add: le_fun_def assert_def demonic_def)

  lemma trs_refinement: "(trs r \<le> trs r') = ((\<forall> x . inpt r x \<longrightarrow> inpt r' x) \<and> (\<forall> x . inpt r x \<longrightarrow> r' x \<le> r x))"
    by (simp add: trs_def assert_demonic_refinement, simp add: le_fun_def)

  lemma "trs (\<lambda> x y . x \<ge> 0) \<le> trs (\<lambda> x y . x = y)"
    by (simp add: trs_def le_fun_def assert_def demonic_def inpt_def)

  lemma "trs (\<lambda> x y . x \<ge> 0) q x = (if q = \<top> then x \<ge> 0 else False)"
     by (auto simp add: trs_def fun_eq_iff assert_def demonic_def inpt_def bot_fun_def)

  lemma "[:r:] \<sqinter> [:r':] = [:r \<squnion> r':]"
    by (simp add: fun_eq_iff demonic_def)

  lemma spec_demonic_choice: "({.p.} o [:r:]) \<sqinter> ({.p'.} o [:r':]) = ({.p \<sqinter> p'.} o [:r \<squnion> r':])"
    by (auto simp add: fun_eq_iff demonic_def assert_def)

  lemma trs_demonic_choice: "trs r \<sqinter> trs r' = trs ((\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r'))"
    proof -
      have [simp]: "inpt ((\<lambda>x y. inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r')) = inpt r \<sqinter> inpt r'"
        by (auto simp add: fun_eq_iff inpt_def)
      have "trs r \<sqinter> trs r' = {. inpt r \<sqinter> inpt r' .} \<circ> [: r \<squnion> r' :]"
        by (simp add: trs_def spec_demonic_choice)
      also have "... = {. inpt r \<sqinter> inpt r' .} \<circ> [: (\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r') :]"
        by (subst assert_demonic_prop, simp)
      also have "... = trs ((\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r'))"
        by (simp add: trs_def)
      finally show ?thesis by simp
    qed

  lemma spec_angelic: "p \<sqinter> p' = \<bottom> \<Longrightarrow> ({.p.} o [:r:]) \<squnion> ({.p'.} o [:r':]) = {.p \<squnion> p'.} o [:(\<lambda> x y . p x \<longrightarrow> r x y) \<sqinter> ((\<lambda> x y . p' x \<longrightarrow> r' x y)):]"
    by (simp add: fun_eq_iff assert_def demonic_def, auto)

  definition "conjunctive (S::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) = (\<forall> Q . S (Inf Q) = INFIMUM Q S)"
  definition "sconjunctive (S::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) = (\<forall> Q . (\<exists> x . x \<in> Q) \<longrightarrow> S (Inf Q) = INFIMUM Q S)"

  lemma [simp]: "conjunctive S \<Longrightarrow> sconjunctive S"
    by (simp add: conjunctive_def sconjunctive_def)

  lemma [simp]: "conjunctive \<top>"
    by (simp add: conjunctive_def)

  lemma conjuncive_demonic [simp]: "conjunctive [:r:]"
    proof (auto simp add: conjunctive_def fun_eq_iff demonic_def)
      fix Q:: "'a set" fix y::'a fix x :: 'b
      assume A: "y \<in> Q"
      assume "r x \<le> Inf Q"
      also from A have "Inf Q \<le> y"
        by (rule Inf_lower)
      finally show "r x \<le> y" by simp
    next
      fix Q:: "'a set" fix x :: 'b
      assume A : "\<forall>y\<in>Q. r x \<le> y"
      show "r x \<le> Inf Q"
        by (rule Inf_greatest, simp add: A)
    qed
      
      term "INF b:X . A"

  lemma sconjunctive_assert [simp]: "sconjunctive {.p.}"
    proof (auto simp add: sconjunctive_def assert_def  image_def, rule antisym, auto)
      fix Q :: "'a set"
      have [simp]: "\<And> x . x \<in> Q \<Longrightarrow> Inf Q \<le> x"
        by (rule Inf_lower, simp)
      have A: "\<And> x . x \<in> Q \<Longrightarrow> p \<sqinter> Inf Q \<le> p \<sqinter> x"
        by (simp, rule_tac y = "Inf Q" in order_trans, simp_all)
      show "p \<sqinter> Inf Q \<le> (INF x:Q. p \<sqinter> x)"
        by (rule Inf_greatest, safe, rule A, simp)
    next
      fix Q :: "'a set"
      fix x :: 'a
      assume A: "x \<in> Q"
      have "(INF x:Q. p \<sqinter> x) \<le> p \<sqinter> x"
        by (rule Inf_lower, cut_tac A, auto)
      also have "... \<le> p"
        by simp
      finally 
      show "(INF x:Q. p \<sqinter> x) \<le> p"
        by simp
   next
      fix Q :: "'a set"
      show "(INF x:Q. p \<sqinter> x) \<le> Inf Q"
        proof (rule Inf_greatest)
          fix x::'a
          assume A: "x \<in> Q"
          have "(INF x:Q. p \<sqinter> x) \<le> p \<sqinter> x"
            by (cut_tac A, rule Inf_lower, blast)
          also have "... \<le> x"
            by simp
         finally show "(INF x:Q. p \<sqinter> x) \<le> x" by simp
       qed
   qed

  lemma sconjunctive_simp: "x \<in> Q \<Longrightarrow> sconjunctive S \<Longrightarrow> S (Inf Q) = INFIMUM Q S"
    by (auto simp add: sconjunctive_def)

  lemma sconjunctive_INF_simp: "x \<in> X \<Longrightarrow> sconjunctive S \<Longrightarrow> S (INFIMUM X Q) = INFIMUM (Q`X) S"
    by (cut_tac x = "Q x" and Q = "Q ` X" in sconjunctive_simp, auto)

  lemma demonic_comp [simp]: "sconjunctive S \<Longrightarrow> sconjunctive S' \<Longrightarrow> sconjunctive (S o S')"
    proof (subst sconjunctive_def, safe)
      fix X :: "'c set"
      fix a :: 'c
      assume [simp]: "sconjunctive S"
      assume [simp]: "sconjunctive S'"
      assume [simp]: "a \<in> X"
      have A: "S' (Inf X) = INFIMUM X S'"
        by (rule_tac x = a in sconjunctive_simp, auto)
      also have B: "S (INFIMUM X S') = INFIMUM (S' ` X) S"
        by (meson \<open>a \<in> X\<close> \<open>sconjunctive S\<close> sconjunctive_INF_simp)
      finally show "(S o S') (Inf X) = INFIMUM X (S \<circ> S')" by simp
    qed

lemma [simp]:"conjunctive S \<Longrightarrow> S (INFIMUM X Q) = (INFIMUM X (S o Q))"
    by (simp add: conjunctive_def)

  lemma conjunctive_simp: "conjunctive S \<Longrightarrow>  S (Inf Q) = INFIMUM Q S"
    by (metis conjunctive_def)

  lemma conjunctive_monotonic [simp]: "sconjunctive S \<Longrightarrow> mono S"
    proof (rule monoI)
      fix a b :: 'a
      assume [simp]: "a \<le> b"
      assume [simp]: "sconjunctive S"
      have [simp]: "a \<sqinter> b = a"
        by (rule antisym, auto)
      have A: "S a = S a \<sqinter> S b"
        by (cut_tac S = S and x = a and Q = "{a, b}" in sconjunctive_simp, simp_all)
      show "S a \<le> S b"
        by (subst A, simp)
    qed

  definition "grd S = - S \<bottom>"

  lemma "grd [:r:] = inpt r"
    by (simp add: fun_eq_iff grd_def demonic_def le_fun_def inpt_def)

  lemma "(S::'a::bot \<Rightarrow> 'b::boolean_algebra) \<le> S' \<Longrightarrow> grd S' \<le> grd S"
    by (simp add: grd_def le_fun_def)

  definition "inp r x = (\<exists> y . r x y)"

  lemma [simp]: "inp (\<lambda>x y. p x \<and> r x y) = p \<sqinter> inp r"
    by (simp add: fun_eq_iff inp_def)

  lemma [simp]: "p \<le> inp r \<Longrightarrow> p \<sqinter> inp r = p"
    by (simp add: fun_eq_iff le_fun_def, auto)


  lemma grd_spec: "grd ({.p.} o [:r:]) = -p \<squnion> inp r"
    by (simp add: grd_def fun_eq_iff demonic_def assert_def le_fun_def inp_def)


  definition "fail S = -(S \<top>)"
  definition "term S = (S \<top>)"
  definition "prec S = - (fail S)"
  definition "rel S = (\<lambda> x y . \<not> S (\<lambda> z . y \<noteq> z) x)"

  lemma rel_spec: "rel ({.p.} o [:r:]) x y = (p x \<longrightarrow> r x y)"
    by (simp add: rel_def demonic_def assert_def le_fun_def)

  lemma prec_spec: "prec ({.p.} o [:r::'a\<Rightarrow>'b\<Rightarrow>bool:]) = p"
    by (auto simp add: prec_def fail_def demonic_def assert_def le_fun_def fun_eq_iff)

  lemma fail_spec: "fail ({.p.} o [:(r::'a\<Rightarrow>'b::boolean_algebra):]) = -p"
    by (simp add: fail_def fun_eq_iff assert_def demonic_def le_fun_def top_fun_def)

  lemma [simp]: "prec ({.p.} o [:(r::'a\<Rightarrow>'b::boolean_algebra):]) = p"
    by (simp add: prec_def fail_spec)

  lemma [simp]: "prec (T::('a::boolean_algebra \<Rightarrow> 'b::boolean_algebra)) = \<top> \<Longrightarrow> prec (S o T) = prec S"
    by (simp add: prec_def fail_def)

  lemma [simp]: "prec [:r::'a \<Rightarrow> 'b::boolean_algebra:] = \<top>"
    by (simp add: demonic_def prec_def fail_def fun_eq_iff)

  lemma prec_rel: "{. p .} \<circ> [: \<lambda>x y. p x \<and> r x y :] = {.p.} o [:r:]"
    by (simp add: fun_eq_iff le_fun_def demonic_def assert_def, auto)


  definition "Fail = \<bottom>"

  lemma Fail_assert_demonic: "Fail = {.\<bottom>.} o [:r:]"
    by (simp add: fun_eq_iff Fail_def assert_def)

  lemma Fail_assert: "Fail = {.\<bottom>.} o [:\<bottom>:]"
    by (rule Fail_assert_demonic)

  lemma fail_comp[simp]: "\<bottom> o S = \<bottom>"
    by (simp add: fun_eq_iff)

  lemma "mono (S::'a::boolean_algebra \<Rightarrow> 'b::boolean_algebra) \<Longrightarrow> (S = Fail) = (fail S = \<top>)"
    proof auto
      show "fail (Fail::'a \<Rightarrow> 'b) = \<top>"
        by (metis Fail_def bot_apply compl_bot_eq fail_def)
    next
      assume A: "mono S"
      assume B: "fail S = \<top>"
      show "S = Fail"
        proof (rule antisym)
          show "S \<le> Fail"
            by (metis (hide_lams, no_types) A B bot.extremum_unique compl_le_compl_iff fail_def le_fun_def monoD top_greatest)
          next
            show "Fail \<le> S"
              by (metis Fail_def bot.extremum)
        qed
   qed

  (* to check - delete? *)
  lemma Inf_not_eq: "Inf {X. \<exists>b. \<not> x b \<and> (X = op \<noteq> b)} = x"
    apply (simp add: fun_eq_iff)
    apply safe
    apply (drule_tac x = "op \<noteq> xa" in spec, simp_all)
    by auto

  lemma sconjunctive_spec: "sconjunctive S \<Longrightarrow> S = {.prec S.} o [:rel S:]"
    apply (simp add: fun_eq_iff assert_def rel_def demonic_def prec_def fail_def le_fun_def, safe)
    apply (drule conjunctive_monotonic)
    apply (drule_tac x = x and y = \<top> in monoE, simp_all)
    apply (simp add: le_fun_def)
    apply (drule conjunctive_monotonic)
    apply (case_tac "x xb", simp)
    apply (drule_tac x = x and y = "(op \<noteq> xb)" in monoE, simp_all)
    apply (simp_all add: le_fun_def)
    apply auto [1]
    apply (simp add: sconjunctive_def)
    apply (drule_tac x = "{X . \<exists> b . \<not> x b \<and> X = op \<noteq> b}" in spec)
    apply (simp add: Inf_not_eq)
    apply(case_tac "x = \<top>", simp_all)
    by auto


  definition "non_magic S = (S \<bottom> = \<bottom>)"

  lemma non_magic_spec: "non_magic ({.p.} o [:r:]) = (p \<le> inpt r)"
    by (simp add: non_magic_def fun_eq_iff inpt_def demonic_def assert_def le_fun_def) 

  lemma sconjunctive_non_magic: "sconjunctive S \<Longrightarrow> non_magic S = (prec S \<le> inpt (rel S))"
    apply (subst non_magic_spec [THEN sym])
    apply (subst sconjunctive_spec [THEN sym])
    by simp_all
  
  definition "implementable S = (sconjunctive S \<and> non_magic S)"

  lemma implementable_spec: "implementable S \<Longrightarrow> \<exists> p r . S = {.p.} o [:r:] \<and> p \<le> inpt r"
    apply (simp add: implementable_def)
    apply (rule_tac x = "prec S" in exI)
    apply (rule_tac x = "rel S" in exI, safe)
    apply (rule sconjunctive_spec, simp)
    by (drule sconjunctive_non_magic, auto)
  

  definition "Skip = (id:: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool))"

  lemma assert_true_skip: "{.\<top>::'a \<Rightarrow> bool.} = Skip"
    by (simp add: fun_eq_iff assert_def Skip_def)

  lemma skip_comp [simp]: "Skip o S = S"
    by (simp add: fun_eq_iff assert_def Skip_def)

  lemma comp_skip[simp]:"S o Skip = S"
    by (simp add: fun_eq_iff assert_def Skip_def)

  lemma [simp]: "{. \<lambda> (x, y) . True .} = Skip"
    by (simp add: fun_eq_iff Skip_def assert_def)

  lemma [simp]: "mono S \<Longrightarrow> mono S' \<Longrightarrow> mono (S o S')"
    by (simp add: mono_def)

  lemma assert_true_skip_a:"{. \<lambda> x . True .} = Skip"
    by (simp add: fun_eq_iff assert_def Skip_def)
    
  lemma assert_false_fail: "{.\<bottom>::'a::boolean_algebra.}  = \<bottom>"
    by (simp add: fun_eq_iff assert_def)

  lemma [simp]: "\<top> o S = \<top>"
    by (simp add: fun_eq_iff)

  lemma left_comp: "T o U = T' o U' \<Longrightarrow> S o T o U = S o T' o U'"
    by (simp add: comp_assoc)

  lemma assert_demonic: "{.p.} o [:r:] = {.p.} o [:\<lambda> x y . p x \<and> r x y:]"
    by (auto simp add: fun_eq_iff assert_def demonic_def le_fun_def)

  lemma "trs r \<sqinter> trs r' = trs (\<lambda> x y . inpt r x \<and> inpt r' x \<and> (r x y \<or> r' x y))"  
    by (auto simp add: fun_eq_iff trs_def assert_def demonic_def inpt_def)


    lemma [simp]: "mono {.p.}"
      apply (simp add: mono_def assert_def)
      apply auto
      apply (rule_tac y = x in order_trans)
      by simp_all

    lemma [simp]: "mono [.p.]"
      apply (simp add: mono_def assume_def)
      apply auto
      apply (rule_tac y = y in order_trans)
      by simp_all

    lemma [simp]: "mono [:r:]"
      by  (auto simp add: mono_def demonic_def le_fun_def)

    lemma [simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (S o T)"
      by simp

    lemma mono_demonic_choice[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (S \<sqinter> T)"
      apply (simp add: mono_def)
      apply auto
      apply (rule_tac y = "S x" in order_trans, simp_all)
      by (rule_tac y = "T x" in order_trans, simp_all)

    lemma [simp]: "mono Skip"
      by (simp add: mono_def Skip_def)

    lemma mono_comp: "mono S \<Longrightarrow> S \<le> S' \<Longrightarrow> T \<le> T' \<Longrightarrow> S o T \<le> S' o T'"
      proof (simp add: le_fun_def, safe)
        fix x
        assume A: "mono S"
        assume B: "\<forall>x. S x \<le> S' x"
        assume "\<forall>x. T x \<le> T' x"
        from this have "T x \<le> T' x" by simp
        from A and this have C: "S (T x) \<le> S (T' x)"
          by (simp add: mono_def)
        from B also have "... \<le> S' (T' x)" by simp
        from C and this show "S (T x) \<le> S' (T' x)" by (rule order_trans)
      qed

  lemma sconjunctive_simp_a: "sconjunctive S \<Longrightarrow> prec S = p \<Longrightarrow> rel S = r \<Longrightarrow> S = {.p.} o [:r:]"
    by (subst sconjunctive_spec, simp_all)

  lemma sconjunctive_simp_b: "sconjunctive S \<Longrightarrow> prec S = \<top> \<Longrightarrow> rel S = r \<Longrightarrow> S = [:r:]"
    by (subst sconjunctive_spec, simp_all add: assert_true_skip)

  lemma [simp]: "sconjunctive Fail"
    apply (simp add: Fail_def sconjunctive_def, auto)
    apply (rule antisym, simp_all)
    by (metis INF_le_SUP SUP_bot empty_iff)

  thm sconjunctive_simp

  lemma sconjunctive_simp_c: "sconjunctive (S::('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool) \<Longrightarrow> prec S = \<bottom> \<Longrightarrow> S = Fail"
    by (drule sconjunctive_spec, simp add: Fail_assert_demonic [THEN sym])

  thm sconjunctive_simp


  lemma demonic_eq_skip: "[: op = :] = Skip"
    apply (simp add: fun_eq_iff)
    by (metis (mono_tags) Skip_def demonic_def id_apply predicate1D predicate1I)

   definition "Havoc = [:\<top>:]"

   definition "Magic = [:\<bottom>::'a \<Rightarrow> 'b::boolean_algebra:]"

  lemma Magic_top: "Magic = \<top>"
    by (simp add: fun_eq_iff Magic_def demonic_def)

   lemma [simp]: "Havoc o (Fail::'a \<Rightarrow> 'b \<Rightarrow> bool) = Fail"
     by (simp add: Havoc_def fun_eq_iff Fail_def demonic_def le_fun_def)

    lemma demonic_havoc: "[: \<lambda>x (x', y). True :] = Havoc"
      by (simp add: fun_eq_iff demonic_def le_fun_def top_fun_def Havoc_def)

   lemma [simp]: "mono Magic"
    by (simp add: Magic_def)

    lemma demonic_false_magic: "[: \<lambda>(x, y) (u, v). False :] = Magic"
      by (simp add: fun_eq_iff demonic_def le_fun_def top_fun_def Magic_def)

   lemma [simp]: "[:r:] o Magic = Magic"
    by (simp add:  fun_eq_iff demonic_def le_fun_def top_fun_def bot_fun_def Magic_def product_def  Skip_def)

   lemma [simp]: "Magic o S = Magic"
    by (simp add:  fun_eq_iff demonic_def le_fun_def top_fun_def Magic_def product_def  Skip_def)

    lemma [simp]: "Havoc \<circ> Magic = Magic"
      by (simp add: Havoc_def)

  lemma "Havoc \<top> = \<top>"
    by (simp add: Havoc_def fun_eq_iff demonic_def le_fun_def top_fun_def)

  lemma [simp]: "Skip p = p"
    by (simp add: Skip_def)


  lemma demonic_pair_skip: "[: \<lambda>(x, y) (u, v). x = u \<and> y = v :] = Skip"
    by (simp add: fun_eq_iff demonic_def Skip_def le_fun_def)

  lemma comp_demonic_demonic: "S o [:r:] o [:r':] = S o [:r OO r':]"
    by (simp add: comp_assoc demonic_demonic)

  lemma comp_demonic_assert: "S o [:r:] o {.p.} = S o {. x. \<forall>y . r x y \<longrightarrow> p y .} o [:r:]"
    by (simp add: comp_assoc demonic_assert_comp)



  lemma [simp]: "prec Skip = (\<top>::'a\<Rightarrow>bool)"
    by (simp add: fun_eq_iff prec_def fail_def Skip_def)


  definition update :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("[-_-]") where
    "[-f-] = [:x \<leadsto> y . y = f x:]"
  syntax
    "_update" :: "patterns => logic => logic"    ("(1[-_./ _-])")
  translations
    "_update (_patterns x xs) F" == "CONST update (CONST id (_abs (_pattern x xs) F))"
    "_update x F" == "CONST update (CONST id (_abs x F))"

  term "[-x,y . (x+y, y-x)-]"
  term "[-x,y . x+y-]"

  lemma update_o_def: "[-f o g-] = [-(\<lambda> x . f (g x))-]"
    by (simp add: o_def)

  lemma update_assert_comp: "[-f-] o {.p.} = {.p o f.} o [-f-]"
    by (simp add: fun_eq_iff update_def demonic_def assert_def le_fun_def)

  lemma update_comp: "[-f-] o [-g-] = [-g o f-]"
    by (simp add: fun_eq_iff update_def demonic_def le_fun_def)

  lemma convert: "(\<lambda> x y . (S::('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) x (f y)) = [-f-] o S"
    by (simp add: fun_eq_iff update_def demonic_def le_fun_def)

  lemma update_id_Skip: "[-id-] = Skip"
    by (simp add: update_def fun_eq_iff demonic_def le_fun_def)

  lemma Fail_assert_update: "Fail = {.\<bottom>.} o [- (Eps \<top>) -]"
    by (simp add: fun_eq_iff Fail_def assert_def)

  lemma fail_assert_update: "\<bottom> = {.\<bottom>.} o [- (Eps \<top>) -]"
    by (simp add: fun_eq_iff assert_def)

  lemma update_fail: "[-f-] o \<bottom> = \<bottom>"
    by (simp add: update_def demonic_def fun_eq_iff le_fun_def)
 
  lemma fail_assert_demonic: "\<bottom> = {.\<bottom>.} o [:\<bottom>:]"
    by (simp add: fun_eq_iff assert_def)

  lemma false_update_fail: "{.\<lambda>x. False.} o [-f-] = \<bottom>"
    by (simp add: fail_assert_update fun_eq_iff assert_def)

  lemma comp_update_update: "S \<circ> [-f-] \<circ> [-f'-] = S \<circ> [- f' o f -]"
    by (simp add: comp_assoc update_comp)

  lemma comp_update_assert: "S \<circ> [-f-] \<circ> {.p.} = S \<circ> {.p o f.} o [-f-]"
    by (simp add: comp_assoc update_assert_comp)

  lemma assert_fail: "{.p::'a::boolean_algebra.} o \<bottom> = \<bottom>"
    by (simp add: assert_def fun_eq_iff)

  lemma angelic_assert: "{:r:} o {.p.} = {:x \<leadsto> y . r x y \<and> p y:}"
    by (simp add: fun_eq_iff angelic_def demonic_def assert_def)

  lemma prec_rel_eq: "p = p' \<Longrightarrow> r = r' \<Longrightarrow> {.p.} o [:r:] = {.p'.} o [:r':]"
    by simp

  lemma prec_rel_le: "p \<le> p' \<Longrightarrow> (\<And> x . p x \<Longrightarrow> r' x \<le> r x) \<Longrightarrow> {.p.} o [:r:] \<le> {.p'.} o [:r':]"
    apply (simp add: le_fun_def demonic_def assert_def, auto)
    by (rule_tac y = "r xa" in order_trans, simp_all)


  lemma assert_update_eq: "({.p.} o [-f-] = {.p'.} o [-f'-]) = (p = p' \<and> (\<forall> x. p x \<longrightarrow> f x = f' x))"
    apply (simp add: fun_eq_iff assert_def demonic_def update_def le_fun_def)
    by auto

  lemma update_eq: "([-f-] = [-f'-]) = (f = f')"
    apply (simp add: fun_eq_iff assert_def demonic_def update_def le_fun_def)
    by auto

  lemma spec_eq_iff: 
    shows spec_eq_iff_1: "p = p' \<Longrightarrow> f = f' \<Longrightarrow> {.p.} o [-f-] = {.p'.} o [-f'-]" 
    and spec_eq_iff_2: "f = f' \<Longrightarrow> [-f-] = [-f'-]"
    and spec_eq_iff_3: "p = (\<lambda> x . True) \<Longrightarrow> f = f' \<Longrightarrow> {.p.} o [-f-] = [-f'-]"
    and spec_eq_iff_4: "p = (\<lambda> x . True) \<Longrightarrow> f = f' \<Longrightarrow> [-f-] = {.p.} o [-f'-]"
    by (simp_all add: assert_true_skip_a)

  lemma spec_eq_iff_a: 
    shows"(\<And> x . p x = p' x) \<Longrightarrow> (\<And> x . f x = f' x) \<Longrightarrow> {.p.} o [-f-] = {.p'.} o [-f'-]" 
    and "(\<And> x . f x = f' x) \<Longrightarrow> [-f-] = [-f'-]"
    and "(\<And> x . p x) \<Longrightarrow> (\<And> x . f x = f' x) \<Longrightarrow> {.p.} o [-f-] = [-f'-]"
    and "(\<And> x . p x) \<Longrightarrow>(\<And> x . f x = f' x) \<Longrightarrow> [-f-] = {.p.} o [-f'-]"
    apply (subgoal_tac "p = p' \<and> f = f'")
    apply simp
    apply (simp add: fun_eq_iff)
    apply (subgoal_tac "f = f'")
    apply simp
    apply (simp add: fun_eq_iff)

    apply (subgoal_tac "p = (\<lambda> x. True) \<and> f = f'")
    apply (simp add: assert_true_skip_a)
    apply (simp add: fun_eq_iff)
    apply (subgoal_tac "p = (\<lambda> x. True) \<and> f = f'")
    apply (simp add: assert_true_skip_a)
    by (simp add: fun_eq_iff)

 lemma spec_eq_iff_prec: "p = p' \<Longrightarrow> (\<And> x . p x \<Longrightarrow> f x = f' x) \<Longrightarrow> {.p.} o [-f-] = {.p'.} o [-f'-]"
    by (simp add: update_def fun_eq_iff assert_def demonic_def le_fun_def, auto)

  lemma sconjunctiveE: "sconjunctive S \<Longrightarrow> (\<exists> p r . S = {. p .} o [: r ::'a \<Rightarrow> 'b \<Rightarrow> bool:])"
    by (drule sconjunctive_spec, blast)

  lemma non_magic_comp [simp]: "non_magic S \<Longrightarrow> non_magic S' \<Longrightarrow> non_magic (S o S')"
    by (simp add: non_magic_def)


  lemma implementable_comp[simp]: "implementable S \<Longrightarrow> implementable S' \<Longrightarrow> implementable (S o S')"
    by (simp add: implementable_def)

  lemma nonmagic_assert: "non_magic {.p::'a::boolean_algebra.}"
    by (simp add: non_magic_def assert_def)
  

end
