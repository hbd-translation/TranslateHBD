section{*\label{sec_Refinement}Refinement Calculus and Monotonic Predicate Transformers*}

theory Refinement imports Main
begin
text{*
  In this section we introduce the basics of refinement calculus \cite{back-wright-98}.
  Part of this theory is a reformulation of some definitions from \cite{preoteasa:back:2010a},
  but here they are given for predicates, while \cite{preoteasa:back:2010a} uses
  sets.
*}
 
notation
    bot ("\<bottom>") and
    top ("\<top>") and
    inf (infixl "\<sqinter>" 70)
    and sup (infixl "\<squnion>" 65)

subsection{*Basic predicate transformers*}

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

syntax 
    "_demonic" :: "patterns => patterns => logic => logic" ("([:_\<leadsto>_._:])")
translations
    "_demonic x y t" == "(CONST demonic (_abs x (_abs y t)))"

syntax 
    "_angelic" :: "patterns => patterns => logic => logic" ("({:_ \<leadsto> _._:})")
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
    
lemma demonic_refinement: "r' \<le> r \<Longrightarrow> [:r:] \<le> [:r':]"
  apply (simp add: le_fun_def demonic_def)
  using order_trans by blast

  
definition "inpt r x = (\<exists> y . r x y)"



definition trs ::  "('a => 'b \<Rightarrow> bool) => ('b \<Rightarrow> bool) => 'a \<Rightarrow> bool" ("{: _ :]" [0] 1000) where
  "trs r = {. inpt r.} o [:r:]"

syntax 
    "_trs" :: "patterns => patterns => logic => logic" ("({:_\<leadsto>_._:])")
translations
    "_trs x y t" == "(CONST trs (_abs x (_abs y t)))"


lemma assert_demonic_prop: "{.p.} o [:r:] = {.p.} o [:(\<lambda> x y . p x) \<sqinter> r:]"
  by (auto simp add: fun_eq_iff assert_def demonic_def)

lemma trs_trs: "(trs r) o (trs r') 
  = trs ((\<lambda> s t. (\<forall> s' . r s s' \<longrightarrow> (inpt r' s'))) \<sqinter> (r OO r'))" (is "?S = ?T")
  by (simp add: trs_def inpt_def fun_eq_iff demonic_def assert_def le_fun_def, blast)

lemma prec_inpt_equiv: "p \<le> inpt r \<Longrightarrow> r' = (\<lambda> x y . p x \<and> r x y) \<Longrightarrow> {.p.} o [:r:] = {:r':]"
  by (simp add: fun_eq_iff demonic_def assert_def le_fun_def inpt_def trs_def, auto)

lemma assert_demonic_refinement: "({.p.} o [:r:] \<le> {.p'.} o [:r':]) = (p \<le> p' \<and> (\<forall> x . p x \<longrightarrow> r' x \<le> r x))"
  by  (auto simp add: le_fun_def assert_def demonic_def)
    
lemma spec_demonic_refinement: "({.p.} o [:r:] \<le> [:r':]) = (\<forall> x . p x \<longrightarrow> r' x \<le> r x)"
  by  (auto simp add: le_fun_def assert_def demonic_def)    

lemma trs_refinement: "(trs r \<le> trs r') = ((\<forall> x . inpt r x \<longrightarrow> inpt r' x) \<and> (\<forall> x . inpt r x \<longrightarrow> r' x \<le> r x))"
  by (simp add: trs_def assert_demonic_refinement, simp add: le_fun_def)

lemma demonic_choice: "[:r:] \<sqinter> [:r':] = [:r \<squnion> r':]"
  by (simp add: fun_eq_iff demonic_def)

lemma spec_demonic_choice: "({.p.} o [:r:]) \<sqinter> ({.p'.} o [:r':]) = ({.p \<sqinter> p'.} o [:r \<squnion> r':])"
  by (auto simp add: fun_eq_iff demonic_def assert_def)

lemma trs_demonic_choice: "trs r \<sqinter> trs r' = trs ((\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r'))"
  by (simp add: trs_def inpt_def fun_eq_iff demonic_def assert_def le_fun_def, blast)

lemma spec_angelic: "p \<sqinter> p' = \<bottom> \<Longrightarrow> ({.p.} o [:r:]) \<squnion> ({.p'.} o [:r':]) 
    = {.p \<squnion> p'.} o [:(\<lambda> x y . p x \<longrightarrow> r x y) \<sqinter> ((\<lambda> x y . p' x \<longrightarrow> r' x y)):]"
  by (simp add: fun_eq_iff assert_def demonic_def, auto)

  subsection{*Conjunctive predicate transformers*}

definition "conjunctive (S::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) = (\<forall> Q . S (Inf Q) = INFIMUM Q S)"
  
definition "sconjunctive (S::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) = (\<forall> Q . (\<exists> x . x \<in> Q) \<longrightarrow> S (Inf Q) = INFIMUM Q S)"
  

lemma conjunctive_sconjunctive[simp]: "conjunctive S \<Longrightarrow> sconjunctive S"
  by (simp add: conjunctive_def sconjunctive_def)

lemma [simp]: "conjunctive \<top>"
  by (simp add: conjunctive_def)

lemma conjuncive_demonic [simp]: "conjunctive [:r:]"
  apply (simp add: conjunctive_def demonic_def fun_eq_iff)
  using le_Inf_iff by blast

lemma sconjunctive_assert [simp]: "sconjunctive {.p.}"
  apply (simp add: sconjunctive_def assert_def, safe)
  apply (rule antisym)
   apply (meson inf_le1 inf_le2 le_INF_iff le_Inf_iff le_infI)
  by (metis (mono_tags, lifting) Inf_greatest le_INF_iff le_inf_iff order_refl)

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
    by (rule_tac x = "S' a" in sconjunctive_simp, auto)
  finally show "(S o S') (Inf X) = INFIMUM X (S \<circ> S')" by simp
qed

lemma conjunctive_INF[simp]:"conjunctive S \<Longrightarrow> S (INFIMUM X Q) = (INFIMUM X (S o Q))"
  by (metis INF_image conjunctive_def)

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
      by (cut_tac S = S and x = a and Q = "{a, b}" in sconjunctive_simp, auto )
    show "S a \<le> S b"
      by (subst A, simp)
  qed

definition "grd S = - S \<bottom>"

lemma grd_demonic: "grd [:r:] = inpt r"
  by (simp add: fun_eq_iff grd_def demonic_def le_fun_def inpt_def)
      
lemma "(S::'a::bot \<Rightarrow> 'b::boolean_algebra) \<le> S' \<Longrightarrow> grd S' \<le> grd S"
  by (simp add: grd_def le_fun_def)

lemma [simp]: "inpt (\<lambda>x y. p x \<and> r x y) = p \<sqinter> inpt r"
  by (simp add: fun_eq_iff inpt_def)

(*to remove*)
lemma [simp]: "p \<le> inpt r \<Longrightarrow> p \<sqinter> inpt r = p"
  by (simp add: fun_eq_iff le_fun_def, auto)

lemma grd_spec: "grd ({.p.} o [:r:]) = -p \<squnion> inpt r"
  by (simp add: grd_def fun_eq_iff demonic_def assert_def le_fun_def inpt_def)


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

lemma Fail_fail: "mono (S::'a::boolean_algebra \<Rightarrow> 'b::boolean_algebra) \<Longrightarrow> (S = Fail) = (fail S = \<top>)"
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
    
lemma sconjunctive_spec: "sconjunctive S \<Longrightarrow> S = {.prec S.} o [:rel S:]"
proof (simp add: fun_eq_iff assert_def rel_def demonic_def prec_def fail_def le_fun_def, safe)
  fix x xa
  assume  "sconjunctive S"
  from this have mono: "mono S"
    by (rule conjunctive_monotonic)
  from this have A: "S x \<le> S \<top>"
    by (simp add: monoD)
  assume C: "S x xa"
  from this and A show "S \<top> xa"
    by blast
  fix xb
  from mono have B: "\<not> x xb \<Longrightarrow> S x \<le> S ((\<noteq>) xb)"
    by (rule monoD, blast)
  assume "\<not> S ((\<noteq>) xb) xa"
  from this B C show "x xb"
    by blast
next
  fix xa x
  assume  sconj: "sconjunctive S"
  assume B: "S \<top> xa"
  assume D: "\<forall>xb. \<not> S ((\<noteq>) xb) xa \<longrightarrow> x xb"
  define Q where "Q = { (\<noteq>) b | b . \<not> x b}"
  from sconj have A: "(\<exists>x. x \<in> Q) \<Longrightarrow> S (Inf Q) = (INF x:Q. S x)"
    by (simp add: sconjunctive_def)
  have C: "Inf Q = x"
    apply (simp add: Q_def fun_eq_iff, safe)
    by (drule_tac x = "(\<noteq>) xa" in spec, auto)
  show "S x xa"
  proof cases
    assume "x = \<top>"
    from this B show ?thesis by simp
  next
    assume "x \<noteq> \<top>"
    from this have [simp]: "S x = (INF x:Q. S x)"
      apply (unfold C [symmetric])
      by (rule A, blast)
    show ?thesis
      apply simp
      using D by (simp add: Q_def, blast)
  qed
qed
  
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

lemma assert_rel_skip[simp]: "{. \<lambda> (x, y) . True .} = Skip"
  by (simp add: fun_eq_iff Skip_def assert_def)

lemma [simp]: "mono S \<Longrightarrow> mono S' \<Longrightarrow> mono (S o S')"
  by (simp add: mono_def)

lemma [simp]: "mono {.p::('a \<Rightarrow> bool).}"
  by simp

lemma [simp]: "mono [:r::('a \<Rightarrow> 'b \<Rightarrow> bool):]"
  by simp

lemma assert_true_skip_a: "{. x . True .} = Skip"
  by (simp add: fun_eq_iff assert_def Skip_def)
    
lemma assert_false_fail: "{.\<bottom>::'a::boolean_algebra.}  = \<bottom>"
  by (simp add: fun_eq_iff assert_def)
    

lemma magoc_comp[simp]: "\<top> o S = \<top>"
  by (simp add: fun_eq_iff)

lemma left_comp: "T o U = T' o U' \<Longrightarrow> S o T o U = S o T' o U'"
  by (simp add: comp_assoc)

lemma assert_demonic: "{.p.} o [:r:] = {.p.} o [:x  \<leadsto> y . p x \<and> r x y:]"
  by (auto simp add: fun_eq_iff assert_def demonic_def le_fun_def)

lemma "trs r \<sqinter> trs r' = trs (\<lambda> x y . inpt r x \<and> inpt r' x \<and> (r x y \<or> r' x y))"
  by (auto simp add: fun_eq_iff trs_def assert_def demonic_def inpt_def)


lemma mono_assert[simp]: "mono {.p.}"
  by (metis (no_types, lifting) assert_def inf.cobounded1 inf_le2 le_infI monoI order_trans)

lemma mono_assume[simp]: "mono [.p.]"
  by (metis assume_def monoI sup.orderI sup_idem sup_mono)

lemma mono_demonic[simp]: "mono [:r:]"
  by  (auto simp add: mono_def demonic_def le_fun_def)

lemma mono_comp_a[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (S o T)"
  by simp

lemma mono_demonic_choice[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (S \<sqinter> T)"
  apply (simp add: mono_def)
  apply auto
   apply (rule_tac y = "S x" in order_trans, simp_all)
  by (rule_tac y = "T x" in order_trans, simp_all)

lemma mono_Skip[simp]: "mono Skip"
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

lemma sconj_Fail[simp]: "sconjunctive Fail"
  by (metis Fail_def INF_eq_const all_not_in_conv bot_apply sconjunctive_def)

lemma sconjunctive_simp_c: "sconjunctive (S::('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool) \<Longrightarrow> prec S = \<bottom> \<Longrightarrow> S = Fail"
  by (drule sconjunctive_spec, simp add: Fail_assert_demonic [THEN sym])

lemma demonic_eq_skip: "[: (=) :] = Skip"
  apply (simp add: fun_eq_iff)
  by (metis (mono_tags) Skip_def demonic_def id_apply predicate1D predicate1I)

definition "Havoc = [:\<top>:]"

definition "Magic = [:\<bottom>::'a \<Rightarrow> 'b::boolean_algebra:]"

lemma Magic_top: "Magic = \<top>"
  by (simp add: fun_eq_iff Magic_def demonic_def)
    
lemma [simp]: "Magic \<noteq> Fail"
  by (simp add: Magic_top Fail_def fun_eq_iff)
      
lemma Havoc_Fail[simp]: "Havoc o (Fail::'a \<Rightarrow> 'b \<Rightarrow> bool) = Fail"
  by (simp add: Havoc_def fun_eq_iff Fail_def demonic_def le_fun_def)

lemma demonic_havoc: "[: \<lambda>x (x', y). True :] = Havoc"
  by (simp add: fun_eq_iff demonic_def le_fun_def top_fun_def Havoc_def)

lemma [simp]: "mono Magic"
  by (simp add: Magic_def)

lemma demonic_false_magic: "[: \<lambda>(x, y) (u, v). False :] = Magic"
  by (simp add: fun_eq_iff demonic_def le_fun_def top_fun_def Magic_def)

lemma demonic_magic[simp]: "[:r:] o Magic = Magic"
  by (simp add:  fun_eq_iff demonic_def le_fun_def top_fun_def bot_fun_def Magic_def product_def Skip_def)

lemma magic_comp[simp]: "Magic o S = Magic"
  by (simp add:  fun_eq_iff demonic_def le_fun_def top_fun_def Magic_def product_def Skip_def)
    
lemma hvoc_magic[simp]: "Havoc \<circ> Magic = Magic"
  by (simp add: Havoc_def)

lemma "Havoc \<top> = \<top>"
  by (simp add: Havoc_def fun_eq_iff demonic_def le_fun_def top_fun_def)
    
lemma Skip_id[simp]: "Skip p = p"
  by (simp add: Skip_def)


lemma demonic_pair_skip: "[: x, y \<leadsto> u, v. x = u \<and> y = v :] = Skip"
  by (simp add: fun_eq_iff demonic_def Skip_def le_fun_def)

lemma comp_demonic_demonic: "S o [:r:] o [:r':] = S o [:r OO r':]"
  by (simp add: comp_assoc demonic_demonic)

lemma comp_demonic_assert: "S o [:r:] o {.p.} = S o {. x. \<forall>y . r x y \<longrightarrow> p y .} o [:r:]"
  by (simp add: comp_assoc demonic_assert_comp)

lemma assert_demonic_eq_demonic: "({.p.} o [:r::'a \<Rightarrow> 'b \<Rightarrow> bool:] = [:r:]) = (\<forall> x . p x)"
  by (simp add: fun_eq_iff demonic_def assert_def le_fun_def, blast)

lemma trs_inpt_top: "inpt r = \<top> \<Longrightarrow> trs r = [:r:]"
  by (simp add: trs_def assert_true_skip)

subsection{*Product and Fusion of predicate transformers*}
  
  text{*
  In this section we define the fusion and product operators from \cite{back:butler:1995}. 
  The fusion of two programs $S$ and $T$ is intuitively equivalent with the parallel execution 
  of the two programs. If $S$ and $T$ assign nondeterministically some value to some program 
  variable $x$, then the fusion of $S$ and $T$ will assign a value to $x$ which can be assigned 
  by both $S$ and $T$.
*}

definition fusion :: "(('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool))" (infixl "\<parallel>" 70) where
  "(S \<parallel> S') q x = (\<exists> (p::'a\<Rightarrow>bool) p' . p \<sqinter> p' \<le> q \<and> S p x \<and> S' p' x)"

lemma fusion_demonic: "[:r:] \<parallel> [:r':] = [:r \<sqinter> r':]"
  by (auto simp add: fun_eq_iff fusion_def demonic_def le_fun_def)

lemma fusion_spec: "({.p.} \<circ> [:r:]) \<parallel> ({.p'.} \<circ> [:r':]) = ({.p \<sqinter> p'.} \<circ> [:r \<sqinter> r':])"
  by (auto simp add: fun_eq_iff fusion_def assert_def demonic_def le_fun_def)

lemma fusion_assoc: "S \<parallel> (T \<parallel> U) = (S \<parallel> T) \<parallel> U"
proof (rule antisym, auto simp add: fusion_def)
  fix p p' q s s' :: "'a \<Rightarrow> bool"
  fix a
  assume A: "p \<sqinter> p' \<le> q" and B: "s \<sqinter> s' \<le> p'"
  assume C: "S p a" and D: "T s a" and E: "U s' a"
  from A and B  have F: "(p \<sqinter> s) \<sqinter> s' \<le> q"
    by (simp add: le_fun_def)
  have "(\<exists>v v'. v \<sqinter> v' \<le> (p \<sqinter> s) \<and> S v a \<and> T v' a)"
    by (metis C D order_refl)
  show "\<exists>u u' . u \<sqinter> u' \<le> q \<and> (\<exists>v v'. v \<sqinter> v' \<le> u \<and> S v a \<and> T v' a) \<and> U u' a"
    by (metis F C D E order_refl)
next
  fix p p' q s s' :: "'a \<Rightarrow> bool"
  fix a
  assume A: "p \<sqinter> p' \<le> q" and B: "s \<sqinter> s' \<le> p"
  assume C: "S s a" and D: "T s' a" and E: "U p' a"
  from A and B  have F: "s \<sqinter> (s' \<sqinter> p')  \<le> q"
    by (simp add: le_fun_def)
  have "(\<exists>v v'. v \<sqinter> v' \<le> s' \<sqinter> p' \<and> T v a \<and> U v' a)"
    by (metis D E eq_iff)
  show "\<exists>u u'. u \<sqinter> u' \<le> q \<and> S u a \<and> (\<exists>v v'. v \<sqinter> v' \<le> u' \<and> T v a \<and> U v' a)"
    by (metis F C D E order_refl)
qed

lemma fusion_refinement: "S \<le> T \<Longrightarrow> S' \<le> T' \<Longrightarrow> S \<parallel> S' \<le> T \<parallel> T'"
  by (simp add: le_fun_def fusion_def, metis)

lemma "conjunctive S \<Longrightarrow> S \<parallel> \<top> = \<top>"
  by (auto simp add: fun_eq_iff fusion_def le_fun_def conjunctive_def)

lemma fusion_spec_local: "a \<in> init \<Longrightarrow> ([: x \<leadsto> u, y . u \<in> init \<and> x = y :] \<circ> {.p.} \<circ> [:r:]) \<parallel> ({.p'.} \<circ> [:r':]) 
    = [: x \<leadsto> u, y . u \<in> init \<and> x = y :] \<circ> {.u,x . p (u, x) \<and> p' x.} \<circ> [:u, x \<leadsto> y . r (u, x) y \<and> r' x y:]" (is "?p \<Longrightarrow> ?S = ?T")
proof -
  assume "?p"
  from this have [simp]: "(\<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) \<and> p' x) = (\<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x)) \<sqinter> p'"
     by auto
  have [simp]: "(\<lambda>x (u, y). u \<in> init \<and> x = y) OO (\<lambda>(u, x) y. r (u, x) y \<and> r' x y) = (\<lambda>x (u, y). u \<in> init \<and> x = y) OO r \<sqinter> r'"
    by auto
  have "?S = 
    ({. \<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) .} \<circ> [: \<lambda>x (u, y). u \<in> init \<and> x = y :] \<circ> [: r :]) \<parallel> ({. p' .} \<circ> [: r' :])"
    by (simp add: demonic_assert_comp)
  also have "... =  {. (\<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x)) \<sqinter> p' .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO r \<sqinter> r' :]"
    by (simp add: comp_assoc demonic_demonic fusion_spec)
  also have "... = ?T"
    by (simp add: demonic_assert_comp comp_assoc demonic_demonic fusion_spec)
  finally show ?thesis by simp
qed
  
lemma fusion_demonic_idemp [simp]: "[:r:] \<parallel> [:r:] = [:r:]"
  by (simp add: fusion_demonic)


lemma fusion_spec_local_a: "a \<in> init \<Longrightarrow> ([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]) \<parallel> [:r':] 
    = ([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:u, x \<leadsto> y . r (u, x) y \<and> r' x y:])"
  by (cut_tac p' = "\<top>" and init = init and p = p and r = r and r' = r' in fusion_spec_local, auto simp add:  assert_true_skip)

lemma fusion_local_refinement:
  "a \<in> init \<Longrightarrow> (\<And> x u y . u \<in> init \<Longrightarrow> p' x \<Longrightarrow> r (u, x) y \<Longrightarrow> r' x y) \<Longrightarrow> 
    {.p'.} o (([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]) \<parallel> [:r':]) \<le> [:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]"
proof -
 assume A: "a \<in> init"
 assume [simp]: "(\<And> x u y . u \<in> init \<Longrightarrow> p' x \<Longrightarrow> r (u, x) y \<Longrightarrow> r' x y)"
 have " {. x. p' x \<and> (\<forall>a. a \<in> init \<longrightarrow> p (a, x)) .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO (\<lambda>(u, x) y. r (u, x) y \<and> r' x y) :]
          \<le> {. \<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO r :]"
  by (auto simp add: assert_demonic_refinement)
from this have " {. x. p' x \<and> (\<forall>a. a \<in> init \<longrightarrow> p (a, x)) .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO (\<lambda>(u, x) y. r (u, x) y \<and> r' x y) :]
        \<le> {. \<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) .} \<circ> [: \<lambda>x (u, y). u \<in> init \<and> x = y :] \<circ> [: r :]"
  by (simp add: comp_assoc demonic_demonic)
from this have "{. p' .} \<circ> [: \<lambda>x (u, y). u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: \<lambda>(u, x) y. r (u, x) y \<and> r' x y :] 
        \<le> [: x \<leadsto> u, y. u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: r :]"
  by (simp add: demonic_assert_comp assert_demonic_comp)
from this have "{. p' .} \<circ> ([: x \<leadsto> (u, y) . u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: (u, x) \<leadsto> y . r (u, x) y \<and> r' x y :]) 
      \<le> [: x \<leadsto> (u, y) . u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: r :]"
  by (simp add: comp_assoc [THEN sym])
from A and this show ?thesis 
  by  (unfold fusion_spec_local_a, simp)
qed

lemma fusion_spec_demonic: "({.p.} o [:r:]) \<parallel> [:r':] = {.p.} o [:r \<sqinter> r':]"
  by (cut_tac p = p and p' = \<top> and r = r and r' = r' in fusion_spec, simp add: assert_true_skip)

definition Fusion :: "('c \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool))) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool))" where
   "Fusion S q x = (\<exists> (p::'c \<Rightarrow> 'a \<Rightarrow> bool) . (INF c . p c) \<le> q \<and> (\<forall> c . (S c) (p c) x))"


lemma Fusion_spec: "Fusion (\<lambda> n . {.p n.} \<circ> [:r n:]) = ({.INFIMUM UNIV p.} \<circ> [:INFIMUM UNIV r:])"
  apply (simp add: fun_eq_iff Fusion_def assert_def demonic_def le_fun_def)
  apply safe
  apply blast
  apply blast
  by (rule_tac x = "\<lambda> x y . r x xa y" in exI, auto)
  
lemma Fusion_demonic: "Fusion (\<lambda> n . [:r n:]) = [:INF n . r n:]"
  apply (cut_tac r = r and p = \<top> in Fusion_spec)
  by (simp add: assert_true_skip)

lemma Fusion_refinement: "(\<And> i . S i \<le> T i) \<Longrightarrow> Fusion S \<le> Fusion T"
  apply (simp add: le_fun_def Fusion_def, safe)
  by (rule_tac x = p in exI, auto)

lemma mono_fusion[simp]: "mono (S \<parallel> T)"
  apply (auto simp add: mono_def fusion_def)
  using order_trans by auto
    
lemma mono_Fusion: "mono (Fusion S)"
  by (simp add: mono_def Fusion_def le_fun_def, auto)

definition "prod_pred A B = (\<lambda>(a, b). A a \<and> B b)"
definition Prod :: "(('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) \<Rightarrow> (('c \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> bool)) \<Rightarrow> (('a \<times> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'd \<Rightarrow> bool))"
   (infixr "**" 70)
  where
  "(S ** T) q = (\<lambda> (x, y) . \<exists> p p' . prod_pred p p' \<le> q \<and> S p x \<and> T p' y)" 

lemma mono_prod[simp]: "mono (S ** T)"
  by (auto simp add: mono_def Prod_def)

lemma Prod_spec: "({.p.} o [:r:]) ** ({.p'.} o [:r':]) = {.x,y . p x \<and> p' y.} o [:x, y \<leadsto> u, v . r x u \<and> r' y v:]"
  apply (simp add: Prod_def fun_eq_iff prod_pred_def demonic_def assert_def le_fun_def)
  apply safe
  apply metis
  by metis

lemma Prod_demonic: "[:r:] ** [:r':] = [:x, y \<leadsto> u, v . r x u \<and> r' y v:]"
  apply (simp add: Prod_def fun_eq_iff prod_pred_def demonic_def le_fun_def)
  apply safe
  apply metis
  by metis

lemma Prod_spec_Skip: "({.p.} o [:r:]) ** Skip = {.x,y . p x.} o [:x, y \<leadsto> u, v . r x u \<and> v = y:]"
  apply (cut_tac p = p and r = r and p' = \<top> and r' = "\<lambda> (x::'b) y . x = y" in Prod_spec)
  apply auto
  apply (subgoal_tac "(\<lambda>(x::'c, y::'b) (u::'a, v::'b). r x u \<and> y = v)
     = (\<lambda>(x::'c, y::'b) (u::'a, v::'b). r x u \<and> v = y)")
  by (auto simp add: fun_eq_iff assert_true_skip demonic_eq_skip)

lemma Prod_Skip_spec: "Skip ** ({.p.} o [:r:]) = {.x,y . p y.} o [:x, y \<leadsto> u, v . x = u \<and> r y v:]"
  apply (cut_tac p = \<top> and r = "\<lambda> (x::'a) y . x = y" and p' = p and r' = r in Prod_spec)
  by (auto simp add:assert_true_skip demonic_eq_skip)

 lemma Prod_skip_demonic: "Skip ** [:r:] = [:x, y \<leadsto> u, v . x = u \<and> r y v:]"
  by (cut_tac r = "(=)" and r' = r in Prod_demonic, simp add: demonic_eq_skip)    

 lemma Prod_demonic_skip: "[:r:] ** Skip = [:x, y \<leadsto> u, v . r x u \<and>  y = v:]"
  by (cut_tac r' = "(=)" and r = r in Prod_demonic, simp add: demonic_eq_skip)

lemma Prod_spec_demonic: "({.p.} o [:r:]) **  [:r':] = {.x, y . p x.} o [:x, y \<leadsto> u, v . r x u \<and> r' y v:]"
  by (cut_tac p = p and p' = \<top> and r = r and r' = r' in Prod_spec, simp add: assert_true_skip)

lemma Prod_demonic_spec: "[:r:] ** ({.p.} o [:r':]) = {.x, y . p y.} o [:x, y \<leadsto> u, v . r x u \<and> r' y v:]"
  by (cut_tac p = \<top> and p' = p and r = r and r' = r' in Prod_spec, simp add: assert_true_skip)

lemma pair_eq_demonic_skip: "[: \<lambda>(x, y) (u, v). x = u \<and> v = y :] = Skip"
  by (simp add: fun_eq_iff demonic_def le_fun_def assert_def)

lemma Prod_assert_skip: "{.p.} ** Skip = {.x,y . p x.}"
  apply (cut_tac p = p and  r = "(=)" in Prod_spec_Skip)
  by (simp add: demonic_eq_skip pair_eq_demonic_skip)

lemma Prod_skip_assert: "Skip ** {.p.} = {.x,y . p y.}"
  apply (cut_tac p = p and  r = "(=)" in Prod_Skip_spec)
  by (simp add: demonic_eq_skip demonic_pair_skip)
    
lemma fusion_comute: "S \<parallel> T = T \<parallel> S"
  by (simp add: fusion_def fun_eq_iff, metis inf_commute)

lemma fusion_mono1: "S \<le> S' \<Longrightarrow> S \<parallel> T \<le> S' \<parallel> T"
  by (auto simp add: le_fun_def fusion_def)

lemma prod_mono1: "S \<le> S' \<Longrightarrow> S ** T \<le> S' ** T"
  by (auto simp add: Prod_def le_fun_def)

lemma prod_mono2: "S \<le> S' \<Longrightarrow> T ** S \<le> T ** S'"
  by (auto simp add: Prod_def le_fun_def)

lemma Prod_fusion: "S ** T = ([:x,y \<leadsto> x' . x = x':] o S o [:x \<leadsto> x', y . x = x':]) \<parallel> ([:x, y \<leadsto> y' . y = y':] o T o [:y \<leadsto> x, y' . y = y':])"
proof (simp add: fun_eq_iff Prod_def prod_pred_def fusion_def demonic_def le_fun_def, safe)
  fix x::"'a \<times> 'b \<Rightarrow> bool" fix a :: 'c fix b::'d fix p::"'a \<Rightarrow> bool" fix p' :: "'b \<Rightarrow> bool"
  assume [simp]: "\<forall>a b. p a \<and> p' b \<longrightarrow> x (a, b)"
  assume [simp]: "S p a"
  assume [simp]: "T p' b"
  have [simp]: "[:x\<leadsto>(x', y).x = x':] (\<lambda>x. p (fst x)) = p"
    by (simp add: fun_eq_iff demonic_def, auto)
  have [simp]: "[:y\<leadsto>(x, ya).y = ya:] (\<lambda>x. p' (snd x)) = p'"
    by (simp add: fun_eq_iff demonic_def, auto)
  show "\<exists>p p'. (\<forall>a b. p (a, b) \<and> p' (a, b) \<longrightarrow> x (a, b)) \<and> S ([:x\<leadsto>(x', y).x = x':] p) a \<and> T ([:y\<leadsto>(x, ya).y = ya:] p') b"
    apply (rule_tac x = "\<lambda> x . p (fst x)" in exI)
    apply (rule_tac x = "\<lambda> x . p' (snd x)" in exI)
    by simp
next
  fix x::"'a \<times> 'b \<Rightarrow> bool" fix a :: 'c fix b::'d fix p::"'a \<times> 'b \<Rightarrow> bool" fix p' :: "'a \<times> 'b \<Rightarrow> bool"
  assume [simp]: "  \<forall>a b. p (a, b) \<and> p' (a, b) \<longrightarrow> x (a, b)"
  assume [simp]: "S ([:x\<leadsto>(x', y).x = x':] p) a"
  assume [simp]: " T ([:y\<leadsto>(x, ya).y = ya:] p') b"
  have [simp]: "(\<lambda>a. \<forall>b. p (a, b)) = [:x\<leadsto>(x', y).x = x':] p"
    by (simp add: fun_eq_iff demonic_def, auto)
  have [simp]: "(\<lambda>b. \<forall>a. p' (a, b)) = [:y\<leadsto>(x, ya).y = ya:] p'"
    by (simp add: fun_eq_iff demonic_def, auto)
  show "\<exists>p p'. (\<forall>a b. p a \<and> p' b \<longrightarrow> x (a, b)) \<and> S p a \<and> T p' b"  
    apply (rule_tac x = "\<lambda> a . \<forall> b . p (a, b)" in exI)
    apply (rule_tac x = "\<lambda> b . \<forall> a . p' (a, b)" in exI)
    by simp
qed

lemma refin_comp_right: "(S::'a \<Rightarrow> 'b::order) \<le> T \<Longrightarrow> S o X \<le> T o X"
  by (simp add: le_fun_def)

lemma refin_comp_left: "mono X \<Longrightarrow> (S::'a \<Rightarrow> 'b::order) \<le> T \<Longrightarrow> X o S  \<le> X o T"
  apply (simp add: le_fun_def)
  by (simp add: monoD)

lemma mono_angelic[simp]: "mono {:r:}"
  apply (simp add: angelic_def mono_def le_fun_def)
  by (metis bot.extremum_uniqueI inf.absorb1 inf_le1 inf_left_commute)

lemma [simp]: "Skip ** Magic = Magic"
  by (auto simp add: fun_eq_iff demonic_def le_fun_def top_fun_def Magic_def Prod_def prod_pred_def Skip_def)

lemma [simp]: "S ** Fail = Fail"
  by (auto simp add: fun_eq_iff Prod_def prod_pred_def Fail_def)

lemma [simp]: "Fail ** S = Fail"
  by (auto simp add: fun_eq_iff  Prod_def prod_pred_def Fail_def)

lemma demonic_conj: "[:(r::'a \<Rightarrow> 'b \<Rightarrow> bool):] o (S \<sqinter> S') = ([:r:] o S) \<sqinter> ([:r:] o  S')"
  by (simp add: fun_eq_iff demonic_def product_def Skip_def prod_pred_def le_fun_def assert_def, auto)

 lemma demonic_assume: "[:r:] o [.p.] = [:x \<leadsto> y . r x y \<and> p y:]"
    by (simp add: fun_eq_iff demonic_def product_def Skip_def le_fun_def assume_def, auto)
  
lemma assume_demonic: "[.p.] o [:r:] = [:x \<leadsto> y . p x \<and> r x y:]"
  by (simp add: fun_eq_iff demonic_def product_def Skip_def le_fun_def assume_def, auto)

lemma [simp]: "(Fail::'a::boolean_algebra) \<le> S"
  by (simp add: Fail_def)

lemma prod_skip_skip[simp]: "Skip ** Skip = Skip"
  apply (cut_tac r = "(=)" and r' = "(=)" in Prod_demonic)
  by (simp add: demonic_eq_skip demonic_pair_skip)

lemma fusion_prod: "S \<parallel> T = [:x \<leadsto> y, z . x = y \<and> x = z:] o Prod S T o [:y , z \<leadsto> x . y = x \<and> z = x:]"
  by (simp add: fun_eq_iff fusion_def Prod_def demonic_def prod_pred_def le_fun_def)

lemma [simp]: "prec S = \<top> \<Longrightarrow> prec T = \<top> \<Longrightarrow> prec (S ** T) = \<top>"
  apply (simp add: prec_def fail_def Prod_def fun_eq_iff, safe)
  apply (rule_tac x = \<top> in exI, simp)
  by (rule_tac x = \<top> in exI, simp)

lemma prec_skip[simp]: "prec Skip = (\<top>::'a\<Rightarrow>bool)"
  by (simp add: fun_eq_iff prec_def fail_def Skip_def)

lemma [simp]: "prec S = \<top> \<Longrightarrow> prec T = \<top> \<Longrightarrow> prec (S \<parallel> T) = \<top>"
  by (simp add: fusion_prod)

subsection{*Functional Update*}
  

definition update :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("[-_-]") where
    "[-f-] = [:x \<leadsto> y . y = f x:]"
syntax
    "_update" :: "patterns \<Rightarrow> tuple_args \<Rightarrow> logic"    ("(1[- _ \<leadsto> _ -])")
translations
    "_update x (_tuple_args f F)" == "CONST update ((_abs x (_tuple f F)))"
    "_update x (_tuple_arg F)" == "CONST update (_abs x F)"
    
lemma update_o_def: "[-f o g-] = [-x \<leadsto> f (g x)-]"
  by (simp add: o_def)
    
lemma update_simp: "[-f-] q = (\<lambda> x . q (f x))"
  by (simp add: demonic_def update_def fun_eq_iff, auto)
    

lemma update_assert_comp: "[-f-] o {.p.} = {.p o f.} o [-f-]"
  by (simp add: fun_eq_iff update_def demonic_def assert_def le_fun_def)

lemma update_comp: "[-f-] o [-g-] = [-g o f-]"
  by (simp add: fun_eq_iff update_def demonic_def le_fun_def)

lemma update_demonic_comp: "[-f-] o [:r:] = [:x \<leadsto> y . r (f x) y:]"
  by (simp add: fun_eq_iff update_def demonic_def le_fun_def)    
    
lemma demonic_update_comp: "[:r:] o [-f-] = [:x \<leadsto> y . \<exists> z . r x z \<and> y = f z:]"
  by (simp add: fun_eq_iff update_def demonic_def le_fun_def, auto)    

lemma comp_update_demonic: "S o [-f-] o [:r:] = S o [:x \<leadsto> y . r (f x) y:]"
  by (simp add: comp_assoc update_demonic_comp)

lemma comp_demonic_update: "S o [:r:] o [-f-] = S o [:x \<leadsto> y . \<exists> z . r x z \<and> y = f z:]"
  by (simp add: comp_assoc demonic_update_comp)
        
lemma convert: "(\<lambda> x y . (S::('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) x (f y)) = [-f-] o S"
  by (simp add: fun_eq_iff update_def demonic_def le_fun_def)

lemma prod_update: "[-f-] ** [-g-] = [-x, y \<leadsto> f x, g y -]"
  apply (simp add: update_def Prod_demonic)
  apply (rule_tac f = demonic in  HOL.arg_cong)
  by fast

lemma prod_update_skip: "[-f-] ** Skip = [- x, y \<leadsto> f x, y-]"
  apply (simp add: update_def Prod_demonic_skip)
  apply (rule_tac f = demonic in  HOL.arg_cong)
  by fast

lemma prod_skip_update: "Skip ** [-f-] = [- x, y \<leadsto> x, f y-]"
  apply (simp add: update_def Prod_skip_demonic)
  apply (rule_tac f = demonic in  HOL.arg_cong)
  by fast

lemma prod_assert_update_skip: "({.p.} o [-f-]) ** Skip = {.x,y . p x.} o [- x, y \<leadsto> f x, y-]"
  apply (simp add: update_def Prod_spec_Skip)
  apply (rule_tac f = "(o)  {. \<lambda>(x, y). p x .}" in  HOL.arg_cong)
  apply (rule_tac f = "demonic" in  HOL.arg_cong)
  by fast

lemma prod_skip_assert_update: "Skip ** ({.p.} o [-f-]) = {.x,y . p y.} o [-\<lambda> (x, y) . (x, f y)-]"
  apply (simp add: update_def Prod_Skip_spec)
  apply (rule_tac f = "(o)  {. \<lambda>(x, y). p y .}" in  HOL.arg_cong)
  apply (rule_tac f = "demonic" in  HOL.arg_cong)
  by fast

lemma prod_assert_update: "({.p.} o [-f-]) ** ({.p'.} o [-f'-]) = {.x,y . p x \<and> p' y.} o [-\<lambda> (x, y) . (f x, f' y)-]"
  apply (simp add: update_def Prod_spec)
  apply (rule_tac f = "(o)  {. \<lambda>(x, y). p x \<and> p' y .}" in  HOL.arg_cong)
  apply (rule_tac f = "demonic" in  HOL.arg_cong)
  by (simp add: fun_eq_iff)

lemma update_id_Skip: "[-id-] = Skip"
  by (simp add: update_def fun_eq_iff demonic_def le_fun_def)

lemma prod_assert_assert_update: "{.p.} ** ({.p'.} o [-f-]) = {.x,y . p x \<and> p' y.} o [- x, y \<leadsto> x, f y-]"
  apply (cut_tac p = p and p' = p' and f = id and f' = f in prod_assert_update)
  by (simp add: update_id_Skip)

lemma prod_assert_update_assert: "({.p.} o [-f-])** {.p'.} = {.x,y . p x \<and> p' y.} o [- x, y \<leadsto> f x, y-]"
  apply (cut_tac p = p and p' = p' and f = f and f' = id in prod_assert_update)
  by (simp add: update_id_Skip)

lemma prod_update_assert_update: "[-f-] ** ({.p.} o [-f'-]) = {.x,y . p y.} o [-x, y \<leadsto> f x, f' y-]"
  apply (cut_tac p = \<top> and p' = p and f = f and f' = f' in prod_assert_update)
  by (simp add: assert_true_skip)

lemma prod_assert_update_update: "({.p.} o [-f-])** [-f'-] = {.x,y . p x .} o [- x, y \<leadsto> f x, f' y-]"
  apply (cut_tac p = p and p' = \<top> and f = f and f' = f' in prod_assert_update)
  by (simp add: assert_true_skip)

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

lemma prod_fail: "\<bottom> ** S = \<bottom>"
  by (simp add: fun_eq_iff Prod_def prod_pred_def)

lemma fail_prod: "S ** \<bottom> = \<bottom>"
  by (simp add: fun_eq_iff Prod_def prod_pred_def)

lemma assert_fail: "{.p::'a::boolean_algebra.} o \<bottom> = \<bottom>"
  by (simp add: assert_def fun_eq_iff)

lemma angelic_assert: "{:r:} o {.p.} = {:x \<leadsto> y . r x y \<and> p y:}"
  by (simp add: fun_eq_iff angelic_def demonic_def assert_def)

lemma Prod_Skip_angelic_demonic: "Skip ** ({:r:} o [:r':]) = {:s,x \<leadsto> s',y . r x y \<and> s' = s:} o [:s,x \<leadsto> s',y . r' x y \<and> s' = s:]"
  apply (simp add: fun_eq_iff Prod_def Skip_def angelic_def demonic_def le_fun_def prod_pred_def)
  apply safe
  apply metis
  apply (rule_tac x = "\<lambda> x . x = a" in exI)
  apply (rule_tac x = "\<lambda> b . x (a, b)" in exI)
  by metis

lemma Prod_angelic_demonic_Skip: "({:r:} o [:r':]) ** Skip = {:x, u \<leadsto> y, u' . r x y \<and> u = u':} o  [:x, u \<leadsto> y, u' . r' x y \<and> u = u':]"
  apply (simp add: fun_eq_iff demonic_def angelic_def le_fun_def Skip_def Prod_def prod_pred_def, auto)
  apply (rule_tac x = "\<lambda> a . r' aa a" in exI)
  apply (rule_tac x = "\<lambda> a . a = b" in exI, simp_all)
  by metis

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


lemma trs_prod: "trs r ** trs r' = trs (\<lambda> (x,x') (y,y') . r x y \<and> r' x' y')"
  apply (simp add: trs_def)
  apply (simp add: Prod_spec)
  apply (subgoal_tac "(\<lambda> (x, y).inpt r x \<and> inpt r' y) = ( inpt (\<lambda>(x, x') (y, y'). r x y \<and> r' x' y'))")
  apply (simp_all)
  by (simp add: fun_eq_iff inpt_def)

lemma sconjunctiveE: "sconjunctive S \<Longrightarrow> (\<exists> p r . S = {. p .} o [: r ::'a \<Rightarrow> 'b \<Rightarrow> bool:])"
  by (drule sconjunctive_spec, blast)

lemma sconjunctive_prod [simp]: "sconjunctive S \<Longrightarrow> sconjunctive S' \<Longrightarrow> sconjunctive (S ** S')"
  apply (drule sconjunctiveE)
  apply (drule sconjunctiveE)
  apply safe
  by (simp add: Prod_spec)

lemma nonmagic_prod [simp]: "non_magic S \<Longrightarrow> non_magic S' \<Longrightarrow> non_magic (S ** S')"
  apply (simp add: non_magic_def)
  apply (simp add: Prod_def)
  apply (simp add: fun_eq_iff prod_pred_def le_fun_def, safe)
  apply (case_tac "p = \<bottom>", simp_all)
  apply (simp add: fun_eq_iff)
  apply (case_tac "p' = \<bottom>", simp_all)
  by (simp add: fun_eq_iff)

lemma non_magic_comp [simp]: "non_magic S \<Longrightarrow> non_magic S' \<Longrightarrow> non_magic (S o S')"
  by (simp add: non_magic_def)

lemma implementable_pred [simp]: "implementable S \<Longrightarrow> implementable S' \<Longrightarrow> implementable (S ** S')"
  by (simp add: implementable_def)

lemma implementable_comp[simp]: "implementable S \<Longrightarrow> implementable S' \<Longrightarrow> implementable (S o S')"
  by (simp add: implementable_def)

lemma nonmagic_assert: "non_magic {.p::'a::boolean_algebra.}"
  by (simp add: non_magic_def assert_def)
    
subsection {*Control Statements*}
  
definition "if_stm p S T = ([.p.] o S) \<sqinter> ([.-p.] o T)"
  
definition "while_stm p S = lfp (\<lambda> X . if_stm p (S o X) Skip)"
  
definition "Sup_less x (w::'b::wellorder) = Sup {(x v)::'a::complete_lattice | v . v < w}"
  
lemma Sup_less_upper: "v < w \<Longrightarrow> P v \<le> Sup_less P w"
  by (simp add: Sup_less_def, rule Sup_upper, blast)

lemma Sup_less_least: "(\<And> v . v < w \<Longrightarrow> P v \<le> Q) \<Longrightarrow> Sup_less P w \<le> Q"
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

theorem lfp_wf_induction_b: "mono f \<Longrightarrow> (\<forall> w . (p w) \<le> f (Sup_less p w)) \<Longrightarrow> S \<le> (SUP a. p a) \<Longrightarrow> S \<le> lfp f"
  apply (rule_tac y = "(SUP a. p a)" in order_trans)
   apply simp
    by (rule lfp_wf_induction, simp_all)

lemma [simp]: "mono S \<Longrightarrow> mono (\<lambda>X. if_stm b (S \<circ> X) T)"
  apply (simp add: if_stm_def mono_def le_fun_def)
  apply auto
  by (metis (no_types, lifting) assume_def dual_order.trans inf.coboundedI1 le_supI sup_ge1 sup_ge2)
  
    
definition  "mono_mono F = (mono F \<and> (\<forall> f . mono f \<longrightarrow> mono (F f)))"

theorem lfp_mono [simp]:
  "mono_mono F \<Longrightarrow> mono (lfp F)"
  apply (simp add: mono_mono_def)
  apply (rule_tac f="F" and P = "mono" in lfp_ordinal_induct)
  apply (simp_all add: mono_def)
  apply (intro allI impI SUP_least)
  apply (rule_tac y = "f y" in order_trans)
  apply (auto intro: SUP_upper)
  done
    
lemma if_mono[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (if_stm b S T)"
  by (simp add: if_stm_def)

subsection{*Hoare Total Correctness Rules*}

definition "Hoare p S q = (p \<le> S q)"

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

 
lemma Sup_less_comp: "(Sup_less P) w o S = Sup_less (\<lambda> w . ((P w) o S)) w"
  apply (simp add: Sup_less_def fun_eq_iff, safe)
  apply (rule antisym)
   apply (rule SUP_least, safe, simp)
    apply (rule_tac i = "\<lambda> x . f (S x)" in SUP_upper2, blast, simp)
   apply (rule SUP_least, safe, simp)
  by (rule_tac i = "P v" in SUP_upper2, auto)

  lemma assert_Sup: "{.Sup (X::'a::complete_distrib_lattice set).} = Sup (assert ` X)"
    by (simp add: fun_eq_iff assert_def Sup_inf)

lemma Sup_less_assert: "Sup_less (\<lambda>w. {. (p w)::'a::complete_distrib_lattice .}) w = {.Sup_less p w.}"
  apply (simp add: Sup_less_def assert_Sup image_def)
  by (simp add: setcompr_eq_image)


lemma [simp]: "Sup_less (\<lambda>n x. t x = n) n = (\<lambda> x . (t x < n))"
  by (simp add: Sup_less_def, auto)
    
lemma [simp]: "Sup_less (\<lambda>n. {.x. t x = n.} \<circ> S) n = {.x. t x < n.} \<circ> S"
  apply (simp add: Sup_less_comp [THEN sym])
  by (simp add: Sup_less_assert)

lemma [simp]: "(SUP a. {.x .t x = a.} \<circ> S) = S"
  by (simp add: fun_eq_iff assert_def)

 
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
      
lemma [simp]: "mono x \<Longrightarrow> mono_mono (\<lambda>X . if_stm b (x \<circ> X) Skip)"
  by (simp add: mono_mono_def)


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
      
lemma refinement_hoare: "S \<le> T \<Longrightarrow> Hoare (p::'a::order) S (q) \<Longrightarrow> Hoare p T q"
  apply (simp add: Hoare_def le_fun_def)
  by (rule_tac y = "S q" in order_trans, simp_all)

lemma refinement_hoare_iff: "(S \<le> T) = (\<forall> p q . Hoare (p::'a::order) S (q) \<longrightarrow> Hoare p T q)"
  apply safe
   apply (rule refinement_hoare, simp_all)
  by (simp add: Hoare_def le_fun_def)
    
subsection{*Data Refinement*}
  
lemma data_refinement: "mono S' \<Longrightarrow> (\<forall> x a . \<exists> u . R x a u) \<Longrightarrow>
    {:x, a \<leadsto> x', u . x = x' \<and> R x a u:} o S \<le> S' o {:y, b \<leadsto> y', v . y = y' \<and> R' y b v:} \<Longrightarrow> 
    [:x \<leadsto> x', u . x = x':] o S o [:y, v \<leadsto> y' . y = y' :] 
    \<le> [:x \<leadsto> x', a . x = x':] o S' o [:y, b \<leadsto> y' . y = y' :]"
proof (simp add: fun_eq_iff demonic_def le_fun_def, safe)
  fix x xa b
  assume A: "\<forall>x a. \<exists>u. R x a u"
  assume B: "\<forall>b. S ([: \<lambda>(y, v). (=) y :] x) (xa, b)"
  assume "\<forall>x a b. {:(x, a) \<leadsto> (x', u).x = x' \<and> R x a u:} (S x) (a, b) \<longrightarrow>
                      S' ({:(y, b) \<leadsto> (y', v).y = y' \<and> R' y b v:} x) (a, b)"
      
  from this have C: "{:(x, a) \<leadsto> (x', u).x = x' \<and> R x a u:} (S ([: \<lambda>(y, v). (=) y :] x)) (xa, b) \<Longrightarrow>
                      S' ({:(y, b) \<leadsto> (y', v).y = y' \<and> R' y b v:} ([: \<lambda>(y, v). (=) y :] x)) (xa, b)"
        
    by simp
  from A obtain u where "R xa b u"
    by blast
    
  from this and B have "{:(x, a) \<leadsto> (x', u).x = x' \<and> R x a u:} (S ([: \<lambda>(y, v). (=) y :] x)) (xa, b)"
    apply (simp add: angelic_def fun_eq_iff)
    by blast
      
  from this and C have D: "S' ({:(y, b) \<leadsto> (y', v).y = y' \<and> R' y b v:} ([: \<lambda>(y, v). (=) y :] x)) (xa, b)"
    by simp
      
  have [simp]: "\<And> s t . {:(y, b) \<leadsto> (y', v).y = y' \<and> R' y b v:} ([: \<lambda>(y, v). (=) y :] x) (s,t) 
    \<Longrightarrow> [: \<lambda>(y, b). (=) y :] x (s, t)"
    by (simp add: le_fun_def demonic_def angelic_def fun_eq_iff)
        
  assume "mono S'"
  from this have "S' ({:(y, b) \<leadsto> (y', v).y = y' \<and> R' y b v:} ([: \<lambda>(y, v). (=) y :] x)) \<le> S' ([: \<lambda>(y, b). (=) y :] x)"
    by (rule monoD, simp add: le_fun_def)
    
  from D and this show "S' ([: \<lambda>(y, b). (=) y :] x) (xa, b)"
    by (simp add: le_fun_def)
qed

lemma mono_update[simp]: "mono [- f -]"
  by (simp add: update_def)
  
end
