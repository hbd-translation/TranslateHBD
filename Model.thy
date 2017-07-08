section{*Model of the HBD Algebra*}

theory Model imports AlgebraFeedback Constructive
begin

  datatype Types = int | bool | nat

  datatype Values = Inte (integer : "int option") | Bool (boolean: "bool option") | Nat (natural: "nat option")

  primrec tv :: "Values \<Rightarrow> Types" where
      "tv (Inte i) = int" |
      "tv (Bool b) = bool" |
      "tv (Nat n) = nat"
  
  primrec tp :: "Values list \<Rightarrow> Types list" where
      "tp [] = []" |
      "tp (a # v) = tv a # tp v"

  fun le_val :: "Values \<Rightarrow> Values \<Rightarrow> bool" where
    "(le_val (Inte v) (Inte u)) = (v \<le> u)" |
    "(le_val (Bool v) (Bool u)) = (v \<le> u)" |
    "(le_val (Nat v) (Nat u)) = (v \<le> u)"  |
    "le_val _ _ = False"

  instantiation Values :: order
    begin
      definition le_Values_def: "((v::Values) \<le> u) = le_val v u"
      definition less_Values_def: "((v::Values) < u) = (v \<le> u \<and> \<not> u \<le> v)"
      instance
      proof
        fix x::Values fix y::Values show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
          by (simp add: less_Values_def)

       show "x \<le> x"
          by (case_tac x, simp_all add: le_Values_def less_Values_def)
       

      fix z show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
          apply (case_tac x, simp_all)
          apply (case_tac y, case_tac z, simp_all add: less_option_def le_Values_def less_Values_def)
          apply (case_tac y, simp_all add:  less_option_def le_Values_def less_Values_def)
          apply (case_tac z, simp_all)
          apply (case_tac y, case_tac z, simp_all add:  less_option_def le_Values_def less_Values_def)
          by (case_tac z, simp_all)

      show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
          apply (case_tac x, simp_all)
          apply (case_tac y, simp_all add: less_option_def le_Values_def less_Values_def)
          apply (case_tac y, simp_all add:  less_option_def le_Values_def less_Values_def)
          by (case_tac y, simp_all add:  less_option_def le_Values_def less_Values_def)

     qed
    end

  fun le_list :: "'a::order list \<Rightarrow> 'a::order list \<Rightarrow> bool" where
    "le_list [] [] = True" |
    "le_list (a # x) (b # y) = (a \<le> b \<and> le_list x y)" |
    "le_list _ _ = False"
    
  instantiation list :: (order) order 
    begin
      definition le_list_def: "((v::'a list) \<le> u) = le_list u v"
      definition less_list_def: "((v::'a list) < u) = (v \<le> u \<and> \<not> u \<le> v)"
      instance
      proof
        fix x y show "((x::'a list) < y) = (x \<le> y \<and> \<not> y \<le> x)"
          by (simp add: less_list_def)
        show "x \<le> x"
          by (induction x, simp_all add: le_list_def)

        fix z show "\<And> y z . x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
          apply (induction x, simp_all add: le_list_def)
          apply (case_tac y, simp_all add: le_list_def)
          apply (case_tac y, simp_all)
          by (case_tac z, simp_all, auto)
       show "\<And> y . x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
          apply (induction x, simp_all add: le_list_def)
          apply (case_tac y, simp_all add: le_list_def)
          by (case_tac y, simp_all add: le_list_def, auto)
     qed
   end

  lemma [simp]: "mono integer"
    apply (simp add: mono_def le_Values_def, safe)
    apply (case_tac x, simp_all)
    apply (case_tac y, simp_all)
    apply (case_tac y, simp_all)
    apply (simp add: integer_def)
    apply (case_tac y, simp_all)
    by (simp add: integer_def)

  lemma [simp]: "mono boolean"
    apply (simp add: mono_def le_Values_def, safe)
    apply (case_tac x, simp_all)
    apply (case_tac y, simp_all)
    apply (simp add: boolean_def)
    apply (case_tac y, simp_all)
    apply (case_tac y, simp_all)
    by (simp add: boolean_def)

  lemma [simp]: "mono natural"
    apply (simp add: mono_def le_Values_def, safe)
    apply (case_tac x, simp_all)
    apply (case_tac y, simp_all)
    apply (simp add: natural_def)
    apply (case_tac y, simp_all)
    apply (simp add: natural_def)
    by (case_tac y, simp_all)
      
  definition "has_in_type x  = {f . (dom f = {v . tp v = x})}"
  definition "has_out_type x = {f . (image f (dom f) \<subseteq> Some ` {v . tp v = x})}"
  
  definition "has_in_out_type x y = has_in_type x \<inter> has_out_type y"
  
  definition "ID_f x v = (if tp v = x then Some v else None)"
  
  lemma [simp]: "(tp x = []) = (x = [])"
    by (case_tac x, simp_all)
      
  lemma map_comp_type: "f \<in> has_in_out_type x y \<Longrightarrow> g \<in> has_in_out_type y z \<Longrightarrow> g \<circ>\<^sub>m f \<in> has_in_out_type x z"
    apply (simp add: has_in_out_type_def has_in_type_def has_out_type_def dom_def map_comp_def image_def, auto)
    apply (case_tac "f xa", simp_all)
    apply force
    apply (simp add: subset_eq)
    apply force
    apply (case_tac "f xa", simp_all)
    by force
    
  definition "TI_f f = (SOME x . (\<exists> y . f \<in> has_in_out_type x y))"

  definition "TO_f f = (SOME y . (\<exists> x . f \<in> has_in_out_type x y))"
  
  fun pref :: "Values list \<Rightarrow> Types list \<Rightarrow> Values list" where
    "pref v [] = []" |
    "pref (a # v) (t # x) = (if tv a = t then a # pref v x else undefined)" |
    "pref v x = undefined"

  fun suff :: "Values list \<Rightarrow> Types list \<Rightarrow> Values list" where
    "suff v [] = v" |
    "suff (a # v) (t # x) = (if tv a = t then suff v x else undefined)" |
    "suff v x = undefined"
    
  lemma tp_pref_suff: "\<And> x y . tp v = x @ y \<Longrightarrow> tp (pref v x) = x \<and> tp (suff v x) = y"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)
    
    
  definition "par_f f g v = (if tp v = (TI_f f) @ (TI_f g) then Some (the (f (pref v (TI_f f))) @ (the (g (suff v (TI_f f))))) else None)"
      
  fun some_v:: "Types list \<Rightarrow> Values list" where
    "some_v [] = []" |
    "some_v (int # x) = (Inte undefined) # some_v x" |
    "some_v (bool # x) = (Bool undefined) # some_v x" |
    "some_v (nat # x) = (Nat undefined) # some_v x"
    
  lemma [simp]: "tp (some_v x) = x"
    apply (induction x, auto)
    by (case_tac a, auto)
      
  lemma same_in_type: "f \<in> has_in_type x \<Longrightarrow> f \<in> has_in_type y \<Longrightarrow> x = y"
    apply (simp add: has_in_type_def set_eq_iff dom_def)
    apply (drule_tac x = "some_v x" in spec, simp)
    by (drule_tac x = "some_v x" in spec, simp)

  lemma same_out_type: "f \<in> has_in_type z \<Longrightarrow> f \<in> has_out_type x \<Longrightarrow> f \<in> has_out_type y \<Longrightarrow> x = y"
    apply (simp add: has_out_type_def has_in_type_def set_eq_iff dom_def subset_eq image_def)
    apply (drule_tac x = "some_v z" in spec, simp, safe)
    apply (drule_tac x = "f (some_v z) " in spec, simp, safe, simp_all)
    apply (drule_tac x = "(some_v z) " in spec, simp)
    apply (drule_tac x = "f (some_v z) " in spec, simp, safe, simp_all)
    by (drule_tac x = "(some_v z) " in spec, simp)

  lemma type_has_type:
    assumes A: "f \<in> has_in_out_type x y"
    shows "TI_f f = x" and "TO_f f = y"
    using A apply (simp add: has_in_out_type_def TI_f_def TO_f_def)
    using same_in_type apply blast
    using A apply (simp add: has_in_out_type_def TI_f_def TO_f_def)
    using same_out_type by blast
    
  lemma has_type_out_type: "f \<in> has_in_out_type x y \<Longrightarrow> tp v = x \<Longrightarrow> tp (the (f v)) = y"
    apply (simp add: has_in_out_type_def has_out_type_def has_in_type_def dom_def image_def set_eq_iff subset_eq, safe)
    apply (drule_tac x = v in spec, simp, safe)
    by (drule_tac x = "Some ya" in spec, auto)
    
  lemma tp_append: "tp (v @ u) = tp v @ tp u"
    by (induction v, simp_all)
    
  lemma par_f_type: "f \<in> has_in_out_type x y \<Longrightarrow> g \<in> has_in_out_type x' y' \<Longrightarrow> par_f f g \<in> has_in_out_type (x @ x') (y @ y')"
    apply (subst has_in_out_type_def)
    apply (simp add:  has_in_type_def has_out_type_def dom_def par_f_def  image_def, auto)
    apply (simp_all add: type_has_type)
    apply (frule tp_pref_suff, safe)
    by (simp add: tp_append has_type_out_type)
    
  definition "Dup_f x v = (if tp v = x then Some (v @ v) else None)"
  
  lemma Dup_has_in_out_type: "Dup_f x \<in> has_in_out_type x (x @ x)"
    apply (simp add: has_in_out_type_def has_out_type_def has_in_type_def dom_def Dup_f_def image_def subset_eq, safe)
    using tp_append by blast
    
  definition "Sink_f x v = (if tp v = x then Some [] else None)"

  lemma Sink_has_in_out_type: "Sink_f x \<in> has_in_out_type x []"
    by (simp add: has_in_out_type_def has_out_type_def has_in_type_def dom_def Sink_f_def image_def subset_eq, auto)

  definition "Switch_f x y v = (if tp v = x @ y then Some (suff v x @ pref v x) else None)"

  lemma Switch_has_in_out_type: "Switch_f x y \<in> has_in_out_type (x @ y) (y @ x)"
    apply (simp add: has_in_out_type_def has_out_type_def has_in_type_def dom_def Switch_f_def image_def subset_eq, safe)
    apply (rule_tac x = "suff xaa x @ pref xaa x" in exI)
    using tp_append tp_pref_suff by simp
  
  
  primrec fb_t :: "Types \<Rightarrow> (Values \<Rightarrow> Values) \<Rightarrow> Values" where
    "fb_t int f  = Inte (Lfp (\<lambda> a . integer (f (Inte a))))" |
    "fb_t bool f = Bool (Lfp (\<lambda> a . boolean (f (Bool a))))" |
    "fb_t nat f  = Nat  (Lfp (\<lambda> a . natural (f (Nat a))))"

  definition "fb_f f v =  (if tp v = tl (TI_f f) then Some (tl (the (f ((fb_t (hd (TI_f f)) (\<lambda> a . hd (the (f (a # v))))) # v)))) else None)"


  thm le_Values_def
  thm le_val.simps


  lemma [simp]: "mono Inte"
    by (simp add: mono_def le_Values_def)

  lemma [simp]: "mono Bool"
    by (simp add: mono_def le_Values_def)

  lemma [simp]: "mono Nat"
    by (simp add: mono_def le_Values_def)

  thm monoE
  thm monoI
  thm mono_aD
  lemma [simp]: "mono A \<Longrightarrow> mono B \<Longrightarrow> mono C \<Longrightarrow> mono_a f\<Longrightarrow> mono_a (\<lambda>a b. C (f (A a) (B b)))"
    apply (subst mono_a_def, safe)
    apply (rule monoD, simp_all)
    apply (rule_tac f = f in  mono_aD, simp_all)
    apply (rule monoD, simp_all)
    by (rule monoD, simp_all)


  lemma fb_t_commute: "mono_a f \<Longrightarrow> mono_a g  
    \<Longrightarrow> fb_t t  (\<lambda> b . f (fb_t t' (\<lambda> a . (g (fb_t t (f a))) a)) b) = fb_t t (\<lambda> b . f (fb_t t' (g b)) b)"
    apply (case_tac t', simp_all)
    apply (case_tac t, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (case_tac t, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (case_tac t, simp_all)
    apply (subst Lfp_commute, simp_all)
    apply (subst Lfp_commute, simp_all)
    by (subst Lfp_commute, simp_all)


  lemma fb_t_eq_type: "(\<And> a . tv a = t \<Longrightarrow> f a = g a) \<Longrightarrow> fb_t t f = fb_t t g"
    by (case_tac t, simp_all)
  

    
  lemma [simp]: "tv (fb_t t f) = t"
     by (case_tac t, simp_all)
      
  lemma has_type_type_in: "f v = Some u \<Longrightarrow> f \<in> has_in_out_type x y \<Longrightarrow> tp v = x"
    by (simp add: has_in_out_type_def has_in_type_def, auto)

  lemma has_type_type_in_a: "f v = None \<Longrightarrow> f \<in> has_in_out_type x y \<Longrightarrow> tp v \<noteq> x"
    apply (simp add: has_in_out_type_def has_in_type_def dom_def)
    apply (unfold set_eq_iff, safe)
    by (drule_tac x = v in spec, simp)
    
  lemma has_type_defined: "f \<in> has_in_out_type x y \<Longrightarrow> tp v = x \<Longrightarrow> \<exists> u . f v = Some u"
    by (simp add: has_in_out_type_def has_in_type_def, auto)
    
  lemma tp_tail: "tp (tl x) = tl (tp x)"
    by (induction x, simp_all)
  
  lemma fb_type: "f \<in> has_in_out_type (t # x) (t # y) \<Longrightarrow> fb_f f \<in> has_in_out_type x y"
    apply (subst has_in_out_type_def)
    apply (simp add: has_out_type_def has_in_type_def fb_f_def dom_def image_def subset_eq, safe)
    apply (simp_all add: type_has_type)
    apply (frule_tac v = "(fb_t t (\<lambda>a::Values. hd (the (f (a # xa)))) # xa)" in has_type_out_type)
    by (simp_all add: tp_append tp_tail)
    
  lemma [simp]: "TI_f (Switch_f x y) = x @ y"
    using Switch_has_in_out_type type_has_type(1) by blast

  lemma ID_f_type[simp]: "ID_f ts \<in> has_in_out_type ts ts"
    by (simp add: ID_f_def has_in_out_type_def has_in_type_def has_out_type_def dom_def Image_def subset_eq)

    
  lemma [simp]: "TI_f (ID_f ts) = ts"
    using ID_f_type type_has_type(1) by blast
    
  lemma [simp]: "tp v = ts \<Longrightarrow> ID_f ts v = Some v"
    by (simp add: ID_f_def)
    
  lemma fb_switch_aux: "f \<in>  has_in_out_type (t' # t # ts) ( t' # t # ts') \<Longrightarrow>
      par_f (Switch_f [t'] [t]) (ID_f ts') \<circ>\<^sub>m (f \<circ>\<^sub>m par_f (Switch_f [t] [t']) (ID_f ts)) = 
        (\<lambda> v . (if tp v = t # t' # ts then case v of a # b # v' \<Rightarrow> (case f (b # a # v') of Some (c # d # u) \<Rightarrow> Some (d # c # u)) else None))"
    apply (simp add: fun_eq_iff par_f_def Switch_f_def map_comp_def, safe)
    apply (case_tac x, simp_all)
    apply (case_tac list, simp_all)
    apply (cut_tac f = f and v = "aa # a # lista" and x = "t' # t # ts" in has_type_defined, simp_all, safe, simp)
    apply (simp add: fun_eq_iff par_f_def Switch_f_def map_comp_def, safe)
    apply (case_tac u, simp_all)
    apply (case_tac list, simp_all)
    apply (cut_tac v= "aa # a # lista" in has_type_out_type, simp_all)
    apply simp
    apply (case_tac u, simp_all)
    apply (case_tac list, simp_all)
    apply (cut_tac v= "aa # a # lista" in has_type_out_type, simp_all)
    apply simp
    apply (case_tac x, simp_all)
    by (case_tac list, simp_all)

       
  lemma TI_f_fb_f[simp]: "f \<in>  has_in_out_type (t # ts) ( t # ts') \<Longrightarrow> TI_f (fb_f f) = ts"
    using fb_type type_has_type(1) by blast
    
  declare [[show_types=false]]

  lemma fb_t_type: "fb_t t (\<lambda>a. if tv a = t then f a else g a) = fb_t t f"
    by (case_tac t, simp_all)

  lemma le_values_same_type:  "a \<le> b \<Longrightarrow> tv a = tv b"
    apply (simp add: le_Values_def)
    apply (case_tac a, simp_all)
    apply (case_tac b, simp_all)
    apply (case_tac b, simp_all)
    by (case_tac b, simp_all)

  thm has_type_out_type

  definition "mono_f = {f . (\<forall> x y . le_list x y \<longrightarrow> le_list (the (f x)) (the (f y)))}"

  lemma [simp]: "le_list v v"
    by (induction v, auto)



  lemma le_pref: "\<And> v x . le_list u v \<Longrightarrow> le_list (pref u x) (pref v x)"
    apply (induction u)
    apply (case_tac v, simp_all)
    apply (case_tac v, simp_all)
    apply (case_tac x, simp_all, safe)
    using le_values_same_type by auto

  lemma le_suff: "\<And> v x . le_list u v \<Longrightarrow> le_list (suff u x) (suff v x)"
    apply (induction u)
    apply (case_tac v, simp_all)
    apply (case_tac v, simp_all)
    apply (case_tac x, simp_all, safe)
    using le_values_same_type by auto


  lemma le_list_append: "\<And> y . le_list x y \<Longrightarrow> le_list x' y' \<Longrightarrow> le_list (x @ x') (y @ y')"
    apply (induction x, simp_all)
    apply (case_tac y, simp_all)
    by (case_tac y, simp_all)

  thm monoD

  lemma mono_fD: "f \<in> mono_f \<Longrightarrow> le_list x y \<Longrightarrow> le_list (the (f x)) (the (f y))"
    by (simp add: mono_f_def)

  lemma le_values_list_same_type: "\<And> (y::Values list) . le_list x y \<Longrightarrow> tp x = tp y"
    apply (induction x, simp_all)
    apply (case_tac y, simp_all add: le_list_def)
    apply (case_tac y, simp_all, safe)
    by (simp add: le_values_same_type)

  lemma map_comp_mono: "f \<in> mono_f \<Longrightarrow> g \<in> mono_f \<Longrightarrow> (\<And> x y . tp x = tp y \<Longrightarrow> f x = None \<Longrightarrow> f y = None) \<Longrightarrow> (\<And> x y . tp x = tp y \<Longrightarrow> g x = None \<Longrightarrow> g y = None) \<Longrightarrow> g \<circ>\<^sub>m f \<in> mono_f"
    apply (subst mono_f_def, safe)
    apply (simp add: map_comp_def)
    apply (case_tac "f x", simp_all)
    apply (case_tac "f y", simp_all)
    apply (metis le_values_list_same_type option.simps(3))
    apply (case_tac "f y", simp_all)
    apply (metis le_values_list_same_type option.simps(3))
    apply (case_tac "g a", simp_all)
    apply (case_tac "g aa", simp_all)
    apply (metis mono_fD option.sel)
    by (metis (no_types, lifting) mem_Collect_eq mono_f_def option.sel)


  lemma par_mono: "f \<in> mono_f \<Longrightarrow> g \<in> mono_f \<Longrightarrow> (\<And> x y . tp x  = tp y \<Longrightarrow> f x = None \<Longrightarrow> f y = None) \<Longrightarrow> (\<And> x y . tp x  = tp y \<Longrightarrow> g x = None \<Longrightarrow> g y = None) \<Longrightarrow> par_f f g \<in> mono_f"
    apply (subst mono_f_def, simp, safe)
    apply (simp add: par_f_def, safe)
    apply (case_tac "f (pref x (TI_f f))", simp_all)
    apply (case_tac "f (pref y (TI_f f))", simp_all)
    apply (case_tac "g (suff x (TI_f f))", simp_all)
    apply (case_tac "g (suff y (TI_f f))", simp_all)
    apply (rule le_list_append, simp_all)
    apply (drule_tac f = g and x = "suff x (TI_f f)" and y = "suff y (TI_f f)" in mono_fD)
    apply (rule le_suff, simp_all)
    apply (case_tac "f (pref y (TI_f f))", simp_all)
    apply (metis (no_types, hide_lams) le_list_append le_pref le_suff mono_fD option.sel)
    apply (metis (no_types, hide_lams) le_list_append le_pref le_suff mono_fD option.sel)

    apply (case_tac "f (pref y (TI_f f))", simp_all)
    apply (metis (no_types, hide_lams) le_list_append le_pref le_suff mono_fD option.sel)

    apply (case_tac "g (suff x (TI_f f))", simp_all)
    apply (case_tac "g (suff y (TI_f f))", simp_all)
    
    apply (rule le_list_append, simp_all)
    apply (drule_tac f = f and x = "pref x (TI_f f)" and y = "pref y (TI_f f)" in mono_fD)
    apply (rule le_pref, simp_all)

    apply (metis (no_types, hide_lams) le_list_append le_pref le_suff mono_fD option.sel)

    apply (case_tac "g (suff y (TI_f f))", simp_all)
    apply (metis (no_types, hide_lams) le_list_append le_pref le_suff mono_fD option.sel)

    apply (rule le_list_append)
    apply (drule_tac f = f and x = "pref x (TI_f f)" and y = "pref y (TI_f f)" in mono_fD)
    apply (rule le_pref, simp_all)
    apply (drule_tac f = g and x = "suff x (TI_f f)" and y = "suff y (TI_f f)" in mono_fD)
    apply (rule le_suff, simp_all)
    by (simp_all add: le_values_list_same_type)

  lemma mono_f_emono: "f \<in> mono_f \<Longrightarrow> (\<And> x y . tp x  = tp y \<Longrightarrow> f x = None \<Longrightarrow> f y = None) \<Longrightarrow> mono A \<Longrightarrow> mono B \<Longrightarrow> emono (\<lambda>a. A (hd (the (f (B a # x)))))"
    apply (simp add: emono_def, safe)
    apply (rule_tac f = A in monoD, simp_all)
    apply (case_tac "(f (B xa # x))", simp_all)
    apply (case_tac "(f (B y # x))", simp_all)
    apply (metis le_values_same_type mono_def option.simps(3) tp.simps(2))
    apply (case_tac "(f (B y # x))", simp_all)
    apply (metis le_values_same_type mono_def option.simps(3) tp.simps(2))
    apply (drule_tac x = "B xa # x" and y = "B y # x" in mono_fD, simp add: le_Values_def)
    apply (cut_tac f = B in monoD, simp_all add: le_Values_def)
    apply (case_tac a, simp_all)
    apply (case_tac aa, simp_all)
    by (case_tac aa, simp_all)

  lemma mono_fb_t_aux: "f \<in> mono_f \<Longrightarrow>
    le_list x y \<Longrightarrow> (\<And>x y. tp x = tp y \<Longrightarrow> f x = None \<Longrightarrow> f y = None) \<Longrightarrow> mono (A::'a::order \<Rightarrow> 'b::fin_cpo) \<Longrightarrow> mono B
      \<Longrightarrow> B (Lfp (\<lambda>a. A (hd (the (f (B a # x)))))) \<le> B (Lfp (\<lambda>a. A (hd (the (f (B a # y))))))"
    apply (rule_tac f = B in monoD, simp_all)
    apply (rule  Lfp_mono)
    apply (rule mono_f_emono)
    apply simp
    apply blast
    apply simp_all
    apply (rule mono_f_emono)
    apply simp
    apply blast
    apply simp_all
    apply (case_tac "(f (B a # x))", simp_all)
    apply (case_tac "(f (B a # y))", simp_all)
    apply (metis le_values_list_same_type option.simps(3) tp.simps(2))
    apply (case_tac "(f (B a # y))", simp_all)
    apply (metis le_values_list_same_type option.simps(3) tp.simps(2))

    apply (drule_tac x = "(B a # x)" and y = "(B a # y)" in mono_fD, simp_all)
    apply (case_tac aa, simp_all)
    apply (case_tac ab, simp_all)
    apply (case_tac ab, simp_all)
    by (rule_tac f = A in monoD, simp_all)

  thm mono_fb_t_aux [of f x y integer]

  lemma mono_fb_f: "f \<in> mono_f \<Longrightarrow> le_list x y \<Longrightarrow> (\<And> x y . tp x  = tp y \<Longrightarrow> f x = None \<Longrightarrow> f y = None) 
    \<Longrightarrow>  fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # x)))) \<le> fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # y))))"
    by (case_tac "hd (TI_f f)", simp_all add: mono_fb_t_aux)


  lemma fb_mono: "f \<in> mono_f \<Longrightarrow> (\<And> x y . tp x  = tp y \<Longrightarrow> f x = None \<Longrightarrow> f y = None) \<Longrightarrow> fb_f f \<in> mono_f"
    apply (subst mono_f_def, simp, safe)
    apply (simp add: fb_f_def, safe)
    apply (simp_all add: le_values_list_same_type)
    apply (case_tac "(f (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # x)))) # x))", simp_all)
    apply (case_tac "(f (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # y)))) # y))", simp_all)
    apply (subgoal_tac "tp (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # y)))) # y) = tp (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # x)))) # x)")
    apply (metis option.distinct(1))
    apply (simp_all add: le_values_list_same_type)
    apply (case_tac "(f (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # y)))) # y))", simp_all)
    apply (subgoal_tac "tp (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # y)))) # y) = tp (fb_t (hd (TI_f f)) (\<lambda>a. hd (the (f (a # x)))) # x)")
    apply (metis option.distinct(1))
    apply (simp_all add: le_values_list_same_type)
    apply (frule_tac x = "fb_t (hd (TI_f f)) (\<lambda>a::Values. hd (the (f (a # x)))) # x" and y = "fb_t (hd (TI_f f)) (\<lambda>a::Values. hd (the (f (a # y)))) # y" in mono_fD, simp_all)
    apply (rule mono_fb_f)
    apply simp
    apply simp
    apply blast
    by (metis hd_Cons_tl le_list.elims(2) le_list.simps(2) list.distinct(1) list.sel(2))
    
  lemma mono_f_mono_a[simp]: "f \<in> mono_f \<Longrightarrow> f \<in>  has_in_out_type (t # t' # ts) ts' \<Longrightarrow> tp v = ts \<Longrightarrow> mono_a (\<lambda>a b. hd (the (f (b # a # v))))"
    apply (simp add: mono_a_def, safe)
    apply (case_tac "f (b # a # v)", simp_all)
    apply (case_tac "f (b' # a' # v)", simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule has_type_type_in_a, simp_all, safe)
    apply (simp add: le_values_same_type)
    apply (simp add: le_values_same_type)
    apply (case_tac "f (b' # a' # v)", simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule has_type_type_in_a, simp_all, safe)
    apply (simp add: le_values_same_type)
    apply (simp add: le_values_same_type)
    apply (case_tac aa, simp_all)
    apply (case_tac ab, simp_all)
    apply (frule_tac v = "b # a # v" in has_type_out_type, simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule_tac v = "b' # a' # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "b' # a' # v" and f = f in  has_type_type_in, simp_all, safe)
    apply (case_tac ab, simp_all)
    apply (frule_tac v = "b # a # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "b # a # v" and f = f in  has_type_type_in, simp_all, safe)
    apply (frule_tac v = "b' # a' # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "b' # a' # v" and f = f in  has_type_type_in, simp_all, safe)
    apply (simp add: mono_f_def)
    apply (drule_tac x = "b # a # v" in spec)
    by (drule_tac x = "b' # a' # v" in spec, simp_all add: le_list_def)

  lemma mono_f_mono_a_b[simp]: "f \<in> mono_f \<Longrightarrow> f \<in>  has_in_out_type (t # t' # ts) ts' \<Longrightarrow> tp v = ts \<Longrightarrow> mono_a (\<lambda>a b. hd (tl (the (f (a # b # v)))))"
    apply (simp add: mono_a_def, safe)
    apply (case_tac "f (a # b # v)", simp_all)
    apply (case_tac "f (a' # b' # v)", simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule has_type_type_in_a, simp_all, safe)
    apply (simp add: le_values_same_type)
    apply (simp add: le_values_same_type)
    apply (case_tac "f (a' # b' # v)", simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule has_type_type_in_a, simp_all, safe)
    apply (simp add: le_values_same_type)
    apply (simp add: le_values_same_type)
    apply (case_tac aa, simp_all)
    apply (case_tac ab, simp_all)
    apply (frule_tac v = "a # b # v" in has_type_out_type, simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule_tac v = "a' # b' # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "a' # b' # v" and f = f in  has_type_type_in, simp_all, safe)
    apply (case_tac ab, simp_all)
    apply (frule_tac v = "a # b # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "a # b # v" and f = f in  has_type_type_in, simp_all, safe)
    apply (frule_tac v = "a' # b' # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "a' # b' # v" and f = f in  has_type_type_in, simp_all, safe)

    apply (case_tac list, simp_all)
    apply (case_tac lista, simp_all)

    apply (frule_tac v = "a # b # v" in has_type_out_type, simp_all)
    apply (frule has_type_type_in, simp_all, safe)
    apply (frule_tac v = "a' # b' # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "a' # b' # v" and f = f in  has_type_type_in, simp_all, safe)

    apply (case_tac lista, simp_all)

    apply (frule_tac v = "a # b # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "a # b # v" and f = f in  has_type_type_in, simp_all, safe)
    apply (frule_tac v = "a' # b' # v" in has_type_out_type, simp_all)
    apply (frule_tac v = "a' # b' # v" and f = f in  has_type_type_in, simp_all, safe)


    apply (simp add: mono_f_def)
    apply (drule_tac x = "a # b # v" in spec)
    by (drule_tac x = "a' # b' # v" in spec, simp_all add: le_list_def)

  lemma [simp]: "Switch_f x y \<in> mono_f"
    apply (simp add: Switch_f_def mono_f_def, auto)
    apply (rule le_list_append)
    apply (simp add: le_suff)
    apply (simp add: le_pref)
    by (simp_all add: le_values_list_same_type)

  lemma [simp]: "ID_f x \<in> mono_f"
    apply (simp add: ID_f_def mono_f_def, auto)
    by (simp_all add: le_values_list_same_type)

  lemma has_type_None: "f \<in> has_in_out_type x y \<Longrightarrow> tp u = tp v \<Longrightarrow> f u = None \<Longrightarrow> f v = None"
    by (metis has_type_type_in has_type_type_in_a option.exhaust)

    
  lemma fb_f_commute: "f \<in> mono_f \<Longrightarrow> f \<in>  has_in_out_type (t' # t # ts) ( t' # t # ts') \<Longrightarrow>
      fb_f (fb_f (par_f (Switch_f [t'] [t]) (ID_f ts') \<circ>\<^sub>m (f \<circ>\<^sub>m par_f (Switch_f [t] [t']) (ID_f ts)))) = (fb_f (fb_f f))"
    proof -
      assume [simp]: "f \<in> mono_f"
      assume [simp]: "f \<in>  has_in_out_type (t' # t # ts) ( t' # t # ts')"
      have TI_f_f[simp]: "TI_f f = t' # t # ts"
        using \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> type_has_type(1) by blast
      
      define g where "g \<equiv> (\<lambda> v . (if tp v = t # t' # ts then case v of a # b # v' \<Rightarrow> (case f (b # a # v') of Some (c # d # u) \<Rightarrow> Some (d # c # u)) else None))"

      have A[simp]: "(par_f (Switch_f [t'] [t]) (ID_f ts') \<circ>\<^sub>m (f \<circ>\<^sub>m par_f (Switch_f [t] [t']) (ID_f ts))) = g"
        by (simp add: g_def fb_switch_aux)

      have [simp]: "g \<in>  has_in_out_type (t # t' # ts) ( t # t' # ts')"
        apply (subst A [THEN sym])
        apply (rule_tac y = "t' # t # ts'" in map_comp_type)
        apply (rule_tac y = "t' # t # ts" in map_comp_type, simp_all)
        apply (cut_tac x = "[t,t']" and y = "[t',t]" and x' = ts and y' = ts and f = "Switch_f [t] [t']" and g = "ID_f ts" in par_f_type, simp_all)
        apply (metis (no_types, lifting) Cons_eq_append_conv Switch_has_in_out_type)
        apply (cut_tac x = "[t',t]" and y = "[t,t']" and x' = ts' and y' = ts' and f = "Switch_f [t'] [t]" and g = "ID_f ts'" in par_f_type, simp_all)
        by (metis (no_types, lifting) Cons_eq_append_conv Switch_has_in_out_type)

      have B: "\<And>x y. tp x = tp y \<Longrightarrow> (f \<circ>\<^sub>m par_f (Switch_f [t] [t']) (ID_f ts)) x = None \<Longrightarrow> (f \<circ>\<^sub>m par_f (Switch_f [t] [t']) (ID_f ts)) y = None"
        apply (simp add: map_comp_def)
        apply (case_tac "par_f (Switch_f [t] [t']) (ID_f ts) x", simp_all)
        apply (case_tac "par_f (Switch_f [t] [t']) (ID_f ts) y", simp_all)
        apply (simp add: par_f_def)
        apply (case_tac "tp y = t # t' # ts", simp_all)
        apply (case_tac "par_f (Switch_f [t] [t']) (ID_f ts) y", simp_all)
          proof -
            fix x :: "Values list" and y :: "Values list" and a :: "Values list" and aa :: "Values list"
            assume a1: "f a = None"
            assume a2: "par_f (Switch_f [t] [t']) (ID_f ts) y = Some aa"
            assume a3: "par_f (Switch_f [t] [t']) (ID_f ts) x = Some a"
            assume a4: "tp x = tp y"
            have "f \<in> has_in_type (t' # t # ts) \<inter> has_out_type (t' # t # ts')"
              using \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_in_out_type_def by blast
            then have f5: "dom f = {vs. tp vs = t' # t # ts}"
              by (simp add: has_in_type_def)
            then have f6: "tp a \<noteq> t' # t # ts"
              using a1 by blast
            have f7: "\<forall>f fa vs. if tp vs = TI_f f @ TI_f fa then par_f f fa vs = Some (the (f (pref vs (TI_f f))) @ the (fa (suff vs (TI_f f)))) else par_f f fa vs = None"
              by (simp add: par_f_def)
            then have f8: "tp x = TI_f (Switch_f [t] [t']) @ TI_f (ID_f ts) \<or> Some a = Some aa"
              using a3 by fastforce
            have "\<forall>f ts tsa vs. f \<notin> has_in_out_type ts tsa \<or> tp vs \<noteq> ts \<or> tp (the (f vs)) = tsa"
              using has_type_out_type by satx
            then have f9: "tp (pref x (TI_f (Switch_f [t] [t']))) \<noteq> [t] @ [t'] \<or> tp (the (Switch_f [t] [t'] (pref x (TI_f (Switch_f [t] [t']))))) = [t'] @ [t]"
              using Switch_has_in_out_type by blast
            { assume "f aa \<noteq> None"
              { assume "Some a \<noteq> Some aa \<and> tp a \<noteq> tp aa"
                moreover
                { assume "Some a \<noteq> Some aa \<and> tp (the (Switch_f [t] [t'] (pref x (TI_f (Switch_f [t] [t']))))) \<noteq> tp (the (Switch_f [t] [t'] (pref y (TI_f (Switch_f [t] [t'])))))"
                  then have "tp aa = t' # t # ts \<longrightarrow> Some a \<noteq> Some aa \<and> tp (the (ID_f ts (suff x (TI_f (Switch_f [t] [t']))))) \<noteq> ts \<or> Some a \<noteq> Some aa \<and> tp (the (ID_f ts (suff y (TI_f (Switch_f [t] [t']))))) \<noteq> ts"
                    using f9 f8 f7 a4 a2 tp_append tp_pref_suff by force }
                ultimately have "tp aa \<noteq> t' # t # ts"
                  using f8 f7 a4 a3 a2 tp_append tp_pref_suff by force }
              then have "tp aa \<noteq> t' # t # ts"
                using f6 by force
              then have "f aa = None"
                using f5 by blast }
            then show "f aa = None"
              by blast
          qed

        
      have [simp]: "g \<in>  mono_f"
        apply (subst A [THEN sym])
        apply (rule map_comp_mono)
        apply (rule map_comp_mono, simp_all)
        apply (rule par_mono, simp_all)
        apply (simp add: Switch_f_def, auto)
        apply (simp add: ID_f_def, auto)
        apply (simp add: par_f_def, auto)
        using \<open>(f::Values list \<Rightarrow> Values list option) \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_None apply blast
        apply (rule par_mono, simp_all)
        apply (simp add: Switch_f_def, auto)
        apply (simp add: ID_f_def, auto)
        apply (rule B, simp_all)
        by (simp add: par_f_def, auto)
        
      have [simp]: "TI_f g = t # t' # ts"
        using \<open>g \<in> has_in_out_type (t # t' # ts) (t # t' # ts')\<close> type_has_type(1) by blast

      define fbt where "fbt \<equiv> (\<lambda> v . fb_t t' (\<lambda>a . hd (the (f (a # v)))))"
      have fbt_simp: "\<And> v . fbt v = fb_t t' (\<lambda>a . hd (the (f (a # v))))"
        by (simp add: fbt_def)

      have C: "\<And> v . tp v = t # ts \<Longrightarrow> fb_f f v = Some (tl (the (f (fbt v # v))))"
        by (simp add: fb_f_def fun_eq_iff fbt_simp [THEN sym])

      have "\<And> v . tp v \<noteq> t # ts \<Longrightarrow> fb_f f v = None"
        by (simp add: fb_f_def)

      have fb_f_f: "fb_f f = (\<lambda> v . (if tp v = t # ts then Some (tl (the (f (fbt v # v)))) else None))"
        apply (simp add: fun_eq_iff C)
        by (simp add: fb_f_def)
        
(****)
      define fbg where "fbg \<equiv> (\<lambda> v . fb_t t (\<lambda>a . hd (the (g (a # v)))))"
      have fbg_simp: "\<And> v . fbg v = fb_t t (\<lambda>a . hd (the (g (a # v))))"
        by (simp add: fbg_def)

      have D: "\<And> v . tp v = t' # ts \<Longrightarrow> fb_f g v = Some (tl (the (g (fbg v # v))))"
        by (simp add: fb_f_def fun_eq_iff fbg_simp [THEN sym])

      have "\<And> v . tp v \<noteq> t' # ts \<Longrightarrow> fb_f g v = None"
        by (simp add: fb_f_def fun_eq_iff)

      have fb_f_g: "fb_f g = (\<lambda> v . (if tp v = t' # ts then Some (tl (the (g (fbg v # v)))) else None))"
        apply (simp add: fun_eq_iff D)
        by (simp add: fb_f_def)

(****)
        
      define f' where "f' \<equiv> fb_f f"
      
      have [simp]: "TI_f f' = t # ts"
        using \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> f'_def fb_type type_has_type(1) by blast

      define fbt' where "fbt' \<equiv> (\<lambda> v . fb_t t (\<lambda>a . hd (the (f' (a # v)))))"
      have fbt'_simp: "\<And> v . fbt' v = fb_t t (\<lambda>a . hd (the (f' (a # v))))"
        by (simp add: fbt'_def)
      
      have A: "\<And> v . tp v = ts \<Longrightarrow> fb_f f' v = Some (tl (the (f' (fbt' v # v))))"
        by (simp add: fb_f_def fun_eq_iff fbt'_simp [THEN sym])

      have [simp]: "\<And> v . tp v \<noteq> ts \<Longrightarrow> fb_f f' v = None"
        by (simp add: fb_f_def fun_eq_iff fbt'_simp [THEN sym])
        
      define g' where "g' \<equiv> fb_f g"
      
      have [simp]: "TI_f g' = t' # ts"
        using \<open>g \<in> has_in_out_type (t # t' # ts) (t # t' # ts')\<close> fb_type g'_def type_has_type(1) by blast

      define fbg' where "fbg' \<equiv> (\<lambda> v . fb_t t' (\<lambda>a . hd (the (g' (a # v)))))"
      have fbg'_simp: "\<And> v . fbg' v = fb_t t' (\<lambda>a . hd (the (g' (a # v))))"
        by (simp add: fbg'_def)
      
      have B: "\<And> v . tp v = ts \<Longrightarrow> fb_f g' v = Some (tl (the (g' (fbg' v # v))))"
        by (simp add: fb_f_def fun_eq_iff fbg'_simp [THEN sym])

      have [simp]: "\<And> v . tp v \<noteq> ts \<Longrightarrow> fb_f g' v = None"
        by (simp add: fb_f_def fun_eq_iff)

      have [simp]: "\<And> v . tp v = ts \<Longrightarrow> tv (fbt' v) = t"  
        by (simp add: fbt'_def)
        
      have [simp]: "\<And> v. tp v = ts \<Longrightarrow> tv (fbg' v) = t'"
        by (simp add: fbg'_def)
        
      have E: "\<And> a b v . tp v = ts \<Longrightarrow> tv a = t \<Longrightarrow> tv b = t' \<Longrightarrow> tl (tl (the (g (a # b # v)))) = tl (tl (the (f (b # a # v))))"
        apply (simp add: g_def, auto)
        apply (cut_tac f = f and v = "b # a # v" and y = "t' # t # ts'" in has_type_defined, simp_all)
        apply auto
        using \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> apply blast
        by (metis (mono_tags, lifting) \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_out_type list.case_eq_if list.sel(3) list.simps(3) option.sel tp.simps(1) tp.simps(2) tp_tail)

      have AA: "\<And> f b u v . f (if b then u else v) = (if b then f u else f v)"
        by (simp add: fun_eq_iff)

      have g_hd_tl: "\<And> a b v . tv a = t' \<Longrightarrow> tv b = t \<Longrightarrow> tp v = ts \<Longrightarrow> hd (tl (the (g (b # a # v)))) = hd (the (f (a # b # v)))"
        apply (case_tac "f (a # b # v)", simp_all)
        apply (metis \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_defined option.simps(3) tp.simps(2))
        apply (case_tac aa, simp_all)
        apply (metis \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_out_type list.simps(3) option.sel tp.simps(1) tp.simps(2))
        apply (case_tac list, simp_all)
        apply (metis (mono_tags, lifting) \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_out_type list.distinct(1) list.sel(3) option.sel tp.simps(1) tp.simps(2))
        by (simp add: g_def)

      have g_hd: "\<And> a b v . tv a = t' \<Longrightarrow> tv b = t \<Longrightarrow> tp v = ts \<Longrightarrow> hd ((the (g (b # a # v)))) = hd ( tl (the (f (a # b # v))))"
        apply (case_tac "f (a # b # v)", simp_all)
        apply (metis \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_defined option.simps(3) tp.simps(2))
        apply (case_tac aa, simp_all)
        apply (metis \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_out_type list.simps(3) option.sel tp.simps(1) tp.simps(2))
        apply (case_tac list, simp_all)
        apply (metis (mono_tags, lifting) \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> has_type_out_type list.distinct(1) list.sel(3) option.sel tp.simps(1) tp.simps(2))
        by (simp add: g_def)

      have [simp]: "\<And> v . tp v = ts \<Longrightarrow> mono_a (\<lambda>a b. hd (the (f (b # a # v))))"
        using \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> \<open>f \<in> mono_f\<close> mono_f_mono_a by blast

      have [simp]: "\<And> v . tp v = ts \<Longrightarrow> mono_a (\<lambda>a b. hd (tl (the (f (a # b # v)))))"
        using \<open>f \<in> has_in_out_type (t' # t # ts) (t' # t # ts')\<close> \<open>f \<in> mono_f\<close> mono_f_mono_a_b by blast
        

      have [simp]: "\<And> v . tp v = ts \<Longrightarrow> mono_a (\<lambda>a b. hd (the (g (b # a # v))))"
        using \<open>g \<in> has_in_out_type (t # t' # ts) (t # t' # ts')\<close> \<open>g \<in> mono_f\<close> mono_f_mono_a by blast

      have [simp]: "\<And> v . tp v = ts \<Longrightarrow> mono_a (\<lambda>a b. hd (tl (the (g (a # b # v)))))"
        using \<open>g \<in> has_in_out_type (t # t' # ts) (t # t' # ts')\<close> \<open>g \<in> mono_f\<close> mono_f_mono_a_b by blast
        
      have [simp]: "\<And>v . tp v = ts \<Longrightarrow> fbt (fbt' v # v) = fbg' v"
        apply (simp add: fbg'_def g'_def fbt_def fbt'_def f'_def)
        apply (simp add: fb_f_f fb_f_g)
        apply (subst fbt_def)
        apply (subst fbg_def)
        apply (simp add: AA fb_t_type)
        apply (subst fb_t_commute)
        apply (simp_all)
        apply (rule fb_t_eq_type)
        apply (simp add: g_hd_tl)
        apply (subgoal_tac "fb_t t (\<lambda>b. hd (tl (the (f (a # b # v))))) = fb_t t (\<lambda>aa. hd (the (g (aa # a # v))))", simp_all)
        apply (rule fb_t_eq_type)
        by (simp add: g_hd)
        
      have [simp]: "\<And> v . tp v = ts \<Longrightarrow> fbg (fbg' v # v) = fbt' v"
        apply (simp add: fbg'_def g'_def fbt_def fbt'_def f'_def)
        apply (simp add: fb_f_f fb_f_g)
        apply (subst fbt_def)
        apply (subst fbg_def)
        apply (subst fbg_def)
        apply (simp add: AA fb_t_type)
        apply (subst fb_t_commute)
        apply simp_all
        apply (rule fb_t_eq_type)
        apply (simp add: g_hd)
        apply (subgoal_tac "(fb_t t' (\<lambda>b. hd (tl (the (g (a # b # v)))))) = (fb_t t' (\<lambda>aa. hd (the (f (aa # a # v)))))")
        apply simp_all
        apply (rule fb_t_eq_type)
        by (simp add: g_hd_tl)
      
      have F: "\<And> v . tp v = ts \<Longrightarrow> fb_f (fb_f g) v = fb_f (fb_f f) v"
        apply (simp add: f'_def [THEN symmetric] A g'_def [THEN symmetric] B)
        apply (simp add: g'_def f'_def C D)
        by (subst E, simp_all)
        

      have "\<And> v . tp v \<noteq> ts \<Longrightarrow> fb_f (fb_f g) v = fb_f (fb_f f) v"
        by (simp add: f'_def [THEN symmetric] g'_def [THEN symmetric])
        
      from F and this show ?thesis
        by (case_tac "tp v = ts", auto)
    qed
 
  definition "typed_func = (\<Union> x . (\<Union> y . has_in_out_type x y)) \<inter> mono_f"

  typedef func = "typed_func"
    apply (simp add: typed_func_def)
    apply (rule_tac x = "ID_f []" in exI, simp)
    apply (rule_tac x = "[]" in exI)
    apply (rule_tac x = "[]" in exI)
    by simp
    
        
  definition "fb_func f = Abs_func (fb_f (Rep_func f))"

  definition "TI_func f = (TI_f (Rep_func f))"
  definition "TO_func f = (TO_f (Rep_func f))"
  definition "ID_func t = Abs_func (ID_f t)"
  
  definition "comp_func f g = Abs_func ((Rep_func g) \<circ>\<^sub>m (Rep_func f))"

  definition "parallel_func f g = Abs_func (par_f (Rep_func f) (Rep_func g))"

  definition "Dup_func x = Abs_func (Dup_f x)"

  definition "Sink_func x = Abs_func (Sink_f x)"
  definition "Switch_func x y = Abs_func (Switch_f x y)"
  
  lemma [simp]: "ID_f t \<in> typed_func"
    apply (simp add: typed_func_def)
    using ID_f_type by blast

    
  lemma map_comp_typed_func[simp]: "f \<in> typed_func \<Longrightarrow> g \<in> typed_func \<Longrightarrow> TI_f g = TO_f f \<Longrightarrow> (g \<circ>\<^sub>m f) \<in> typed_func"
    apply (simp add: typed_func_def, safe)
    using map_comp_type type_has_type(1) type_has_type(2) apply fastforce
    by (simp add: has_type_None map_comp_mono)

  lemma par_typed_func[simp]: "f \<in> typed_func \<Longrightarrow> g \<in> typed_func \<Longrightarrow> par_f f g \<in> typed_func"
    apply (simp add: typed_func_def, safe)
    using par_f_type type_has_type(1) type_has_type(2) apply fastforce
    by (simp add: has_type_None par_mono)

  lemma fb_typed_func[simp]: "f \<in> typed_func \<Longrightarrow> TI_f f = t # x \<Longrightarrow> TO_f f = t # y \<Longrightarrow> fb_f f \<in> typed_func"
    apply (simp add: typed_func_def, safe)
    using fb_type type_has_type(1) type_has_type(2) apply fastforce
    by (simp add: has_type_None fb_mono)

  lemma [simp]: "Switch_f x y \<in> typed_func"
    apply (simp add: typed_func_def)
    using Switch_has_in_out_type by auto
    
  lemma [simp]: "Dup_f x \<in> mono_f"
    apply (simp add: Dup_f_def mono_f_def, safe)
    apply (simp add: le_list_append)
    using le_values_list_same_type by auto

  lemma [simp]: "Dup_f x \<in> typed_func"
    apply (simp add: typed_func_def)
    using Dup_has_in_out_type by auto

  lemma [simp]: "Sink_f x \<in> mono_f"
    apply (simp add: Sink_f_def mono_f_def, safe)
    using le_values_list_same_type by auto

  lemma [simp]: "Sink_f x \<in> typed_func"
    apply (simp add: typed_func_def)
    using Sink_has_in_out_type by auto

  thm Rep_func
  thm Abs_func_inverse
  thm Rep_func_inverse
  
  lemma map_comp_assoc: "(f \<circ>\<^sub>m g) \<circ>\<^sub>m h = f \<circ>\<^sub>m (g \<circ>\<^sub>m h)"
    apply (simp add: map_comp_def fun_eq_iff, safe)
    by (case_tac "h x", simp_all)

  lemma map_comp_id: "f \<in> has_in_out_type x y \<Longrightarrow> (f \<circ>\<^sub>m ID_f x) = f"
    apply (simp add: fun_eq_iff map_comp_def ID_f_def)
    by (metis has_type_type_in not_Some_eq)

  lemma id_map_comp: "f \<in> has_in_out_type x y \<Longrightarrow> (ID_f y \<circ>\<^sub>m f) = f"
    apply (simp add: fun_eq_iff map_comp_def ID_f_def, safe)
    apply (case_tac "f xa", simp_all)
    by (metis (mono_tags, lifting) ID_f_def has_type_out_type has_type_type_in option.sel)


  lemma [simp]: "\<And> x x' . tp v = x @ x' @ x'' \<Longrightarrow> pref (pref v (x @ x')) x = pref v x"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)

  lemma [simp]: "\<And> x x' . tp v = x @ x' @ x'' \<Longrightarrow> suff (pref v (x @ x')) x = pref (suff v x) x'"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)

  lemma [simp]: "\<And> x x' . tp v = x @ x' @ x'' \<Longrightarrow>suff (suff v x) x' = suff v (x @ x')"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)

  lemma par_f_assoc: "f \<in> has_in_out_type x y \<Longrightarrow> g \<in> has_in_out_type x' y' \<Longrightarrow> h \<in> has_in_out_type x'' y'' \<Longrightarrow>
    par_f (par_f f g) h = par_f f (par_f g h)"
    proof -
      assume A: "f \<in> has_in_out_type x y"
      assume B: "g \<in> has_in_out_type x' y'"
      assume C: "h \<in> has_in_out_type x'' y''"
      have [simp]: "TI_f f = x"
        using A type_has_type(1) by auto
      have [simp]: "TI_f g = x'"
        using B type_has_type(1) by auto
      have [simp]: "TI_f h = x''"
        using C type_has_type(1) by auto

      have "par_f f g \<in>  has_in_out_type (x @ x') (y @ y')"
        using  A B by (simp add: par_f_type)
      from this have [simp]: "TI_f (par_f f g) = x @ x'"
        using type_has_type(1) by auto


      have "par_f g h \<in>  has_in_out_type (x' @ x'') (y' @ y'')"
        using  B C by (simp add: par_f_type)
      from this have [simp]: "TI_f (par_f g h) = x' @ x''"
        using type_has_type(1) by auto

      show ?thesis
        apply (simp add: fun_eq_iff par_f_def type_has_type par_f_type, safe)
        by (simp_all add: tp_pref_suff)
    qed

   lemma "f \<in> has_in_out_type x y \<Longrightarrow> par_f (ID_f []) f = f"
    proof -
      assume A [simp]: "f \<in> has_in_out_type x y"
    show ?thesis
      apply (simp add: fun_eq_iff par_f_def ID_f_def, safe)      
      apply (metis A has_type_type_in_a option.collapse type_has_type(1))
      by (metis ID_f_def A map_comp_id map_comp_simps(1) type_has_type(1))
    qed

   lemma id_par_f: "f \<in> has_in_out_type x y \<Longrightarrow> par_f (ID_f []) f = f"
    proof -
      assume A [simp]: "f \<in> has_in_out_type x y"
    show ?thesis
      apply (simp add: fun_eq_iff par_f_def ID_f_def, safe)      
      apply (metis A has_type_type_in_a option.collapse type_has_type(1))
      by (metis ID_f_def A map_comp_id map_comp_simps(1) type_has_type(1))
    qed

   lemma [simp]: "\<And> x . tp v = x \<Longrightarrow> pref v x = v"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)

   lemma [simp]: "\<And> x . tp v = x \<Longrightarrow> suff v x = []"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)

   lemma par_f_id: "f \<in> has_in_out_type x y \<Longrightarrow> par_f f (ID_f []) = f"
    proof -
      assume A [simp]: "f \<in> has_in_out_type x y"
    show ?thesis
      apply (simp add: fun_eq_iff par_f_def ID_f_def, safe)      
      apply (metis A has_type_type_in_a option.collapse type_has_type(1))
      by (metis A ID_f_def map_comp_id map_comp_simps(1) type_has_type(1))
    qed
  lemma [simp]: "\<And> x . tp v = x @ y \<Longrightarrow> pref v x @ suff v x = v"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)
    
  lemma [simp]: "\<And> x . tp v = x @ x' \<Longrightarrow> tp (pref v x) = x"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)

  lemma [simp]: "\<And> x . tp v = x @ x' \<Longrightarrow> tp (suff v x) = x'"
    apply (induction v, simp_all)
    by (case_tac x, simp_all)
    
  lemma [simp]: "\<And> x . tp u = x \<Longrightarrow> pref (u @ v) x = u"
    apply (induction u, simp_all)
    by (case_tac x, simp_all)


  lemma [simp]: "\<And> x . tp u = x \<Longrightarrow> suff (u @ v) x = v"
    apply (induction u, simp_all)
    by (case_tac x, simp_all)
    
  lemma par_comp_distrib: "f \<in> has_in_out_type x y \<Longrightarrow> g \<in> has_in_out_type y z \<Longrightarrow> 
    f' \<in> has_in_out_type x' y' \<Longrightarrow> g' \<in> has_in_out_type y' z' \<Longrightarrow> 
    par_f g g' \<circ>\<^sub>m par_f f f' = (par_f (g \<circ>\<^sub>m f) (g' \<circ>\<^sub>m f'))"
    proof -
      assume A: "f \<in> has_in_out_type x y"
      assume B: "f' \<in> has_in_out_type x' y'"
      assume C: "g \<in> has_in_out_type y z"
      assume D: "g' \<in> has_in_out_type y' z'"
      have [simp]: "TI_f f = x"
        using A type_has_type(1) by auto
      have [simp]: "TI_f g = y"
        using C type_has_type(1) by auto
      have [simp]: "TI_f f' = x'"
        using B type_has_type(1) by auto
      have [simp]: "TI_f g' = y'"
        using D type_has_type(1) by auto
          
      have [simp]: "TI_f (g \<circ>\<^sub>m f) = x"
        using A C map_comp_type type_has_type(1) by blast

      have [simp]: "TI_f (g' \<circ>\<^sub>m f') = x'"
        using B D map_comp_type type_has_type(1) by blast
        
      have Aa: "\<And> v . tp v = x @ x' \<Longrightarrow> \<exists> u . f (pref v x) = Some u \<and> tp u = y"
         apply (cut_tac A, cut_tac f = f and v = "pref v x" in has_type_defined)
         apply (simp_all)
         by (metis has_type_out_type has_type_type_in option.sel)
         
         
      have Ab: "\<And> v . tp v = x @ x' \<Longrightarrow> \<exists> u . f' (suff v x) = Some u \<and> tp u = y'"
         apply (cut_tac B, cut_tac f = f' and v = "suff v x" in has_type_defined)
         apply (simp_all)
         by (metis has_type_out_type has_type_type_in option.sel)
        
      show ?thesis
        apply (simp add: fun_eq_iff par_f_def, safe)
        apply (frule Aa, safe, simp)
        apply (frule Ab, safe, simp)
        apply (frule Aa, safe, simp)
        apply (frule Ab, safe, simp)
        by (simp add: tp_append)
     qed
     
  lemma TI_f_par: "f \<in> typed_func \<Longrightarrow> g \<in> typed_func \<Longrightarrow> TI_f (par_f f g) = TI_f f  @ TI_f g"
    apply (simp add: typed_func_def, safe)
    apply (frule_tac f = f and g = g in par_f_type, simp_all)
    using type_has_type(1) by auto

  lemma TO_f_par: "f \<in> typed_func \<Longrightarrow> g \<in> typed_func \<Longrightarrow> TO_f (par_f f g) = TO_f f  @ TO_f g"
    apply (simp add: typed_func_def, safe)
    apply (frule_tac f = f and g = g in par_f_type, simp_all)
    using type_has_type(2) by auto

  lemma TI_f_map_comp[simp]: "f \<in> typed_func \<Longrightarrow> g \<in> typed_func \<Longrightarrow> TO_f g = TI_f f \<Longrightarrow> TI_f (f \<circ>\<^sub>m g) = TI_f g"
    apply (simp add: typed_func_def, safe)
    apply (frule_tac f = g and g = f and z = xa in map_comp_type)
    apply (simp add: type_has_type(1) type_has_type(2))
    by (simp add: type_has_type(1))

  lemma TO_f_map_comp[simp]: "f \<in> typed_func \<Longrightarrow> g \<in> typed_func \<Longrightarrow> TO_f g = TI_f f \<Longrightarrow> TO_f (f \<circ>\<^sub>m g) = TO_f f"
    apply (simp add: typed_func_def, safe)
    apply (frule_tac f = g and g = f and z = xa in map_comp_type)
    apply (simp add: type_has_type(1) type_has_type(2))
    by (simp add: type_has_type(2))

  lemma [simp]: "TI_f (Sink_f ts) = ts"
    using Sink_has_in_out_type type_has_type(1) by blast

  lemma [simp]: "TO_f (Sink_f ts) = []"
    using Sink_has_in_out_type type_has_type(2) by blast

  lemma suff_append: "\<And> t . tp x = t \<Longrightarrow> suff (x @ y) t = y"
    apply (induction x, simp_all)
    by (case_tac t, simp_all)

  lemma [simp]: "TI_f (Dup_f x) = x"
    using Dup_has_in_out_type type_has_type(1) by blast


  lemma [simp]: "TO_f (Dup_f x) = (x @ x)"
    using Dup_has_in_out_type type_has_type(2) by blast
        
  lemma [simp]: "pref (x @ y) (tp x) = x"
    by (induction x, simp_all)

  lemma [simp]: "TO_f (Switch_f x y) = (y @ x)"
    using Switch_has_in_out_type type_has_type(2) by blast

  lemma [simp]: "TO_f (ID_f x) = x"
    using ID_f_type type_has_type(2) by blast

  declare TO_f_par [simp]

  declare TI_f_par [simp]

  lemma [simp]: "\<And> ts .  tp x = ts @ ts' @ ts'' \<Longrightarrow> pref (suff x ts) ts' @ suff x (ts @ ts') = suff x ts"
    apply (induction x, simp_all)
    by (case_tac ts, simp_all)


  lemma [simp]: "\<And>ts . tp x = ts \<Longrightarrow>  suff (x @ y) (ts @ ts') = suff y ts'"
    apply (induction x, simp_all)
    by (case_tac ts, simp_all)

  lemma AAA: "S x \<noteq> None \<Longrightarrow> tv a = t \<Longrightarrow> tp x = TI_f S \<Longrightarrow> the ((par_f (ID_f [t]) S) (a # x)) = a # the (S x) "
    by (simp add: par_f_def)

  lemma AAAb: "S x \<noteq> None \<Longrightarrow> tv a = t \<Longrightarrow> tp x = TI_f S \<Longrightarrow> ((par_f (ID_f [t]) S) (a # x)) = Some (a # the (S x))"
    by (simp add: par_f_def)

  lemma pref_suff_append: "\<And> ts . tp x = ts @ ts' \<Longrightarrow> pref x ts @ suff x ts = x"
    apply (induction x)
    by auto

  lemma [simp]: "Lfp (\<lambda> b. a) = a"
    apply (rule lfp_exists)
    by (simp add: is_lfp_def)


  lemma [simp]: "fb_t (tv a) (\<lambda> b . a) = a"
    apply (case_tac "tv a", simp_all)
    apply (case_tac a, simp_all)
    apply (case_tac a, simp_all)
    by (case_tac a, simp_all)

  interpretation func: BaseOperation TI_func TO_func ID_func comp_func parallel_func Dup_func Sink_func Switch_func fb_func
    proof
      fix ts show "TI_func (ID_func ts) = ts"
        by (simp add: TI_func_def ID_func_def Abs_func_inverse)
      fix ts show "TO_func (ID_func ts) = ts"
        by (simp add: TO_func_def ID_func_def Abs_func_inverse)
      fix S S' show " TI_func S' = TO_func S \<Longrightarrow> TI_func (comp_func S S') = TI_func S"
        by (simp add: TI_func_def comp_func_def TO_func_def Rep_func Abs_func_inverse)
        
      fix S S' show " TI_func S' = TO_func S \<Longrightarrow> TO_func (comp_func S S') = TO_func S'"
        by (simp add: TI_func_def comp_func_def TO_func_def Rep_func Abs_func_inverse)
        
      fix S show "comp_func (ID_func (TI_func S)) S = S"
        apply (simp add: TI_func_def comp_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (cut_tac x = S in Rep_func)
        apply (simp add: typed_func_def, safe)
        by (simp add: Rep_func_inverse map_comp_id type_has_type(1))

      fix S show "comp_func S (ID_func (TO_func S)) = S"
        apply (simp add: TI_func_def comp_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (cut_tac x = S in Rep_func)
        apply (simp add: typed_func_def, safe)
        by (simp add: Rep_func_inverse id_map_comp type_has_type(2))

      fix T S R show "TI_func T = TO_func S \<Longrightarrow> TI_func R = TO_func T \<Longrightarrow> comp_func (comp_func S T) R = comp_func S (comp_func T R)"
        by (simp add: comp_func_def Rep_func Abs_func_inverse TI_func_def TO_func_def map_comp_assoc)

      fix S T show "TI_func (parallel_func S T) = TI_func S @ TI_func T"
        by (simp add: TI_func_def parallel_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)

      fix S T show "TO_func (parallel_func S T) = TO_func S @ TO_func T"
        by (simp add: TI_func_def parallel_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)

      fix A B C show "parallel_func (parallel_func A B) C = parallel_func A (parallel_func B C)"
        apply (simp add: TI_func_def parallel_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (cut_tac x = A in Rep_func)
        apply (cut_tac x = B in Rep_func)
        apply (cut_tac x = C in Rep_func)
        apply (simp add: typed_func_def, safe)
        by (subst par_f_assoc, simp_all)

      fix S show "parallel_func (ID_func []) S = S"
        apply (simp add: TI_func_def parallel_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (cut_tac x = S in Rep_func)
        apply (simp add: typed_func_def, safe)
        by (subst id_par_f, simp_all add: Rep_func_inverse)
        
      fix S show " parallel_func S (ID_func []) = S"
        apply (simp add: TI_func_def parallel_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (cut_tac x = S in Rep_func)
        apply (simp add: typed_func_def, safe)
        by (subst par_f_id, simp_all add: Rep_func_inverse)

      fix ts ts' show  "parallel_func (ID_func ts) (ID_func ts') = ID_func (ts @ ts')"
        apply (simp add: TI_func_def parallel_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (rule_tac f = Abs_func in arg_cong)
        by (simp add: par_f_def fun_eq_iff ID_f_def)

      fix S S' T T' show "TO_func S = TI_func S' \<Longrightarrow>
        TO_func T = TI_func T' \<Longrightarrow> comp_func (parallel_func S T) (parallel_func S' T') = parallel_func (comp_func S S') (comp_func T T')"
        apply (simp add: TI_func_def parallel_func_def comp_func_def TO_func_def Rep_func Abs_func_inverse ID_func_def)
        apply (cut_tac x = S in Rep_func)
        apply (cut_tac x = S' in Rep_func)
        apply (cut_tac x = T in Rep_func)
        apply (cut_tac x = T' in Rep_func)
        apply (simp add: typed_func_def type_has_type, safe)
        apply (unfold type_has_type)
        by (subst par_comp_distrib , simp_all)
        
      fix ts show "TI_func (Dup_func ts) = ts"
        by (simp add: TI_func_def Dup_func_def Abs_func_inverse)

      fix ts show "TO_func (Dup_func ts) = ts @ ts"
        by (simp add: TO_func_def Dup_func_def Abs_func_inverse)

      fix ts show "TI_func (Sink_func ts) = ts" and "TO_func (Sink_func ts) = []"
        by (simp_all add: TO_func_def TI_func_def Sink_func_def Abs_func_inverse)
        
      fix ts ts' show "TI_func (Switch_func ts ts') = ts @ ts'" and "TO_func (Switch_func ts ts') = ts' @ ts"
        by (simp_all add: TO_func_def TI_func_def Switch_func_def Abs_func_inverse)
        
      fix ts show "comp_func (Dup_func ts) (parallel_func (Sink_func ts) (ID_func ts)) = ID_func ts"
        apply (simp add: comp_func_def Dup_func_def parallel_func_def ID_func_def Abs_func_inverse Rep_func Sink_func_def)
        apply (rule_tac f = Abs_func in arg_cong)
        apply (simp add: fun_eq_iff map_comp_def, safe)
        apply (case_tac "Dup_f ts x", simp_all)
        apply (simp add: Dup_f_def ID_f_def)
        apply auto [1]
        apply (simp add: par_f_def, safe)
        apply (simp add: Dup_f_def Sink_f_def)
        apply (case_tac " tp x = ts", simp_all)
        using suff_append apply blast
        using Dup_f_def ID_f_def tp_append by auto

      fix ts show "comp_func (Dup_func ts) (Switch_func ts ts) = Dup_func ts"
        apply (simp add: comp_func_def Dup_func_def  Abs_func_inverse Rep_func Switch_func_def)
        apply (rule_tac f = Abs_func in arg_cong)
        by (simp add: fun_eq_iff map_comp_def Dup_f_def Switch_f_def tp_append)

      fix ts show "comp_func (Dup_func ts) (parallel_func (ID_func ts) (Dup_func ts)) 
        = comp_func (Dup_func ts) (parallel_func (Dup_func ts) (ID_func ts))"
        apply (simp add: comp_func_def Dup_func_def parallel_func_def ID_func_def Abs_func_inverse Rep_func)
        apply (rule_tac f = Abs_func in arg_cong)
        by (simp add: fun_eq_iff map_comp_def Dup_f_def par_f_def)

      fix S t' t ts ts' have "TI_func S = t' # t # ts \<Longrightarrow>
        TO_func S = t' # t # ts' \<Longrightarrow>
        (fb_func ^^ (Suc (Suc 0)))
         (comp_func (comp_func (parallel_func (Switch_func [t] [t']) (ID_func ts)) S) (parallel_func (Switch_func [t'] [t]) (ID_func ts'))) =
        (fb_func ^^ (Suc (Suc 0))) S"
        
        apply (simp add: TO_func_def TI_func_def fb_func_def comp_func_def parallel_func_def Rep_func Abs_func_inverse Switch_func_def ID_func_def)
        apply (cut_tac x = S in Rep_func)
        apply (simp add: typed_func_def, safe)
        apply (subst fb_f_commute, simp_all)
        by (simp add: type_has_type(1) type_has_type(2))
        
     from this show "TI_func S = t' # t # ts \<Longrightarrow>
        TO_func S = t' # t # ts' \<Longrightarrow>
        (fb_func ^^ 2)
         (comp_func (comp_func (parallel_func (Switch_func [t] [t']) (ID_func ts)) S) (parallel_func (Switch_func [t'] [t]) (ID_func ts'))) =
        (fb_func ^^ 2) S"
        by (simp add: numeral_2_eq_2)

     fix ts'' show "Switch_func ts (ts' @ ts'') = comp_func (parallel_func (Switch_func ts ts') (ID_func ts'')) (parallel_func (ID_func ts') (Switch_func ts ts''))"
       apply (simp add: Switch_func_def comp_func_def parallel_func_def ID_func_def Abs_func_inverse)
       apply (rule_tac f = Abs_func in arg_cong)
       by (simp add: fun_eq_iff Switch_f_def par_f_def tp_append)

     show "parallel_func (Sink_func ts) (Sink_func ts') = Sink_func (ts @ ts')"
       apply (simp add: Sink_func_def parallel_func_def Abs_func_inverse)
       apply (rule_tac f = Abs_func in arg_cong)
       by (simp add: fun_eq_iff Sink_f_def par_f_def)

    show "Dup_func (ts @ ts') = comp_func (parallel_func (Dup_func ts) (Dup_func ts')) (parallel_func (parallel_func (ID_func ts) (Switch_func ts ts')) (ID_func ts'))"
       apply (simp add: Switch_func_def comp_func_def parallel_func_def ID_func_def Dup_func_def Abs_func_inverse)
       apply (rule_tac f = Abs_func in arg_cong)
       by (simp add: fun_eq_iff Switch_f_def par_f_def Dup_f_def tp_append)       
      
       thm has_type_defined
       
    have [simp]: "\<And> B . Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))"
      by (metis (no_types, lifting) Int_iff Rep_func mem_simps(8) type_has_type(1) type_has_type(2) typed_func_def)
       
    fix ti to ti' to' show "TI_func A = ti \<Longrightarrow> TO_func A = to \<Longrightarrow> TI_func B = ti' \<Longrightarrow> TO_func B = to' 
      \<Longrightarrow> comp_func (comp_func (Switch_func ti ti') (parallel_func B A)) (Switch_func to' to) = parallel_func A B"
       apply (simp add: Switch_func_def comp_func_def parallel_func_def ID_func_def Dup_func_def TI_func_def TO_func_def Rep_func Abs_func_inverse)
       apply (rule_tac f = Abs_func in arg_cong)
       apply (simp add: fun_eq_iff Switch_f_def par_f_def map_comp_def tp_append, auto)
       apply (cut_tac f = "Rep_func B" and x = ti' and y = to' and v = "suff x (TI_f (Rep_func A))" in has_type_defined, simp_all)
       apply (safe, simp_all)
       apply (cut_tac f = "Rep_func A" and x = ti and y = to and v = "pref x (TI_f (Rep_func A))" in has_type_defined, simp_all)
       apply (safe, simp_all)
       apply (cut_tac f = "Rep_func B" and x = ti' and y = to' and v = "suff x (TI_f (Rep_func A))" in has_type_out_type, simp_all)
       apply (cut_tac f = "Rep_func A" and x = ti and y = to and v = "pref x (TI_f (Rep_func A))" in has_type_out_type, simp_all)
       by (cut_tac f = "Rep_func B" and x = ti' and y = to' and v = "suff x (TI_f (Rep_func A))" in has_type_out_type, simp_all)
       
    show "TI_func S = t # ts \<Longrightarrow> TO_func S = t # ts' \<Longrightarrow> TI_func (fb_func S) = ts"
      apply (simp add: TI_func_def fb_func_def TO_func_def Abs_func_inverse Rep_func)
      by (metis \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> fb_type type_has_type(1))

    show "TI_func S = t # ts \<Longrightarrow> TO_func S = t # ts' \<Longrightarrow> TO_func (fb_func S) = ts'"
      apply (simp add: TI_func_def fb_func_def TO_func_def Abs_func_inverse Rep_func)
      by (metis \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> fb_type type_has_type(2))
      
    show "TI_func S = t # TO_func A \<Longrightarrow>
               TO_func S = t # TI_func B \<Longrightarrow>
               fb_func (comp_func (comp_func (parallel_func (ID_func [t]) A) S) (parallel_func (ID_func [t]) B)) = comp_func (comp_func A (fb_func S)) B"
      
      apply (simp add: TI_func_def fb_func_def TO_func_def Abs_func_inverse Rep_func parallel_func_def ID_func_def comp_func_def)
      apply (subst Abs_func_inverse)
      apply (rule map_comp_typed_func)
      apply (simp_all add: Rep_func)
      apply (metis \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> fb_type type_has_type(1))
      apply (rule_tac f = Abs_func in arg_cong)
      apply (simp add: fun_eq_iff, safe)
      apply (subst (3) map_comp_def)
      (*apply (subst (1) fb_f_def, simp, safe)*)
      apply (case_tac "(fb_f (Rep_func S) \<circ>\<^sub>m Rep_func A) x", simp_all)
      apply (simp add: fb_f_def)
      apply (subst TI_f_map_comp)
      apply (simp_all add: Rep_func)
      apply (metis \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> fb_type has_type_out_type has_type_type_in_a map_comp_None_iff option.sel)
      
      apply (simp add: fb_f_def)
      apply (subst TI_f_map_comp)
      apply (simp_all add: Rep_func, safe)
      apply (subst (asm) map_comp_def)
      apply (case_tac " Rep_func A x", simp_all)
      apply (subst (asm) fb_f_def, simp)
      apply (case_tac "tp aa = TO_f (Rep_func A)", simp_all)
      apply (case_tac "(Rep_func S (fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa)))) # aa))")
      apply (simp_all)
      apply (case_tac "tp (fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa)))) # aa) =  t # TO_f (Rep_func A)")
      apply (metis \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> has_type_type_in_a)
      apply simp
      prefer 2
      apply (meson \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> has_type_type_in map_comp_Some_iff)
      proof - 
        fix x a ab aa
        define b where "b \<equiv> fb_t t (\<lambda>a. hd (the ((par_f (ID_f [t]) (Rep_func B) \<circ>\<^sub>m (Rep_func S \<circ>\<^sub>m par_f (ID_f [t]) (Rep_func A))) (a # x))))"

        assume "TI_f (Rep_func S) = t # TO_f (Rep_func A)"
        assume "TO_f (Rep_func S) = t # TI_f (Rep_func B)"
        assume D: "Rep_func S (fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa)))) # aa) = Some ab"
        assume E: "tl ab = a"
        assume "tp x = TI_f (Rep_func A)"
        assume [simp]:"Rep_func A x = Some aa"
        assume"tp aa = TO_f (Rep_func A)"

        have [simp]: "tv b = t"
          by (simp add: b_def)

        have C: "b = fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa))))"
        apply (simp add: b_def)
        apply (rule fb_t_eq_type)
        apply (simp add: map_comp_def)
        apply (subst AAAb, simp_all)
        apply (simp add: \<open>tp x = TI_f (Rep_func A)\<close>)
        apply (case_tac "Rep_func S (a # aa)", simp_all)
        apply (case_tac "aaa", simp_all)
        apply (metis \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> has_type_out_type list.distinct(1) option.sel tp.simps(1) tp.simps(2))
        apply (subst AAAb, simp_all)
        apply (metis \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> has_type_defined has_type_out_type list.sel(3) option.sel tp.simps(2))
        apply (metis \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> has_type_out_type list.inject option.sel tp.simps(2))
        by (metis \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> has_type_out_type list.inject option.sel tp.simps(2))

        obtain  u v where [simp]: "Rep_func S (b # aa) = Some (u # v)"
          apply (case_tac " Rep_func S (b # aa)")
          apply (simp_all)
          apply (simp add: \<open>Rep_func S (fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa)))) # aa) = Some ab\<close> \<open>b = fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa))))\<close>)
          apply (case_tac "a")
          apply simp_all  
          by (metis \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> \<open>tv b = t\<close> has_type_out_type list.distinct(1) option.sel tp.simps(1) tp.simps(2))

        from this have B: "v = a"
          apply (simp add: C D)
          by (cut_tac E, simp)

        have A: "((par_f (ID_f [t]) (Rep_func B) \<circ>\<^sub>m (Rep_func S \<circ>\<^sub>m par_f (ID_f [t]) (Rep_func A))) (b # x)) = Some (u # the (Rep_func B v))"
          apply (simp add: map_comp_def)
          apply (subst AAAb, simp_all)
          apply (simp add: \<open>tp x = TI_f (Rep_func A)\<close>)
          apply (subst AAAb, simp_all)
          apply (metis (mono_tags, lifting) \<open>Rep_func S (b # aa) = Some (u # v)\<close> \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> \<open>tv b = t\<close> has_type_defined has_type_out_type list.sel(3) option.sel tp.simps(2))
          apply (metis \<open>Rep_func S (b # aa) = Some (u # v)\<close> \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> \<open>tv b = t\<close> has_type_out_type list.inject option.sel tp.simps(2))
          by (metis \<open>Rep_func S (b # aa) = Some (u # v)\<close> \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>tp aa = TO_f (Rep_func A)\<close> \<open>tv b = t\<close> has_type_out_type list.sel(3) option.sel tp.simps(2))

        have " Some (tl (the ((par_f (ID_f [t]) (Rep_func B) \<circ>\<^sub>m (Rep_func S \<circ>\<^sub>m par_f (ID_f [t]) (Rep_func A))) (b # x)))) =
           Rep_func B a"
           apply (simp add: A)
           apply (simp add: B)
           apply (case_tac " Rep_func B a", simp_all)
           by (metis \<open>Rep_func S (fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa)))) # aa) = Some ab\<close> \<open>TI_f (Rep_func S) = t # TO_f (Rep_func A)\<close> \<open>TO_f (Rep_func S) = t # TI_f (Rep_func B)\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> \<open>\<And>thesis. (\<And>u v. Rep_func S (b # aa) = Some (u # v) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>b = fb_t t (\<lambda>a. hd (the (Rep_func S (a # aa))))\<close> \<open>tl ab = a\<close> \<open>tp aa = TO_f (Rep_func A)\<close> \<open>tv b = t\<close> has_type_out_type has_type_type_in_a list.sel(3) option.sel tp.simps(2))
        from this show " Some (tl (the ((par_f (ID_f [t]) (Rep_func B) \<circ>\<^sub>m (Rep_func S \<circ>\<^sub>m par_f (ID_f [t]) (Rep_func A)))
                           (fb_t t (\<lambda>a. hd (the ((par_f (ID_f [t]) (Rep_func B) \<circ>\<^sub>m (Rep_func S \<circ>\<^sub>m par_f (ID_f [t]) (Rep_func A))) (a # x)))) # x)))) =
           Rep_func B a"
           by (simp add: b_def)
      qed

     show "TI_func S = t # ts \<Longrightarrow> TO_func S = t # ts' \<Longrightarrow> fb_func (parallel_func S T) = parallel_func (fb_func S) T"
      apply (simp add: TI_func_def fb_func_def TO_func_def Abs_func_inverse Rep_func parallel_func_def ID_func_def comp_func_def)
      apply (subgoal_tac " (fb_f (par_f (Rep_func S) (Rep_func T))) = (par_f (fb_f (Rep_func S)) (Rep_func T))")
      apply simp_all
      apply (simp add: fun_eq_iff, safe)
      apply (simp add: par_f_def, auto)
      apply (subst fb_f_def, auto)
      prefer 2
      apply (subst TI_f_par)
      apply (simp_all add: Rep_func)
      apply (metis TI_f_fb_f \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close>)
      prefer 2
      apply (metis Rep_func TI_f_fb_f TI_f_par \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> append.simps(2) fb_f_def list.sel(3))
      apply (simp add: fb_f_def)
      proof -
        fix x
        assume Ca: "TI_f (Rep_func S) = t # ts"
        assume "TO_f (Rep_func S) = t # ts'"
        assume "TI_f (fb_f (Rep_func S)) = ts"
        assume "tp x = ts @ TI_f (Rep_func T)"
        from this have A: "x = pref x ts @ suff x ts"
          by (simp add: pref_suff_append)
        have [simp]: "\<And>a . tv a = t \<Longrightarrow> (pref (a # pref x ts @ suff x ts) (TI_f (Rep_func S))) = a # pref x ts"
          using A \<open>TI_f (Rep_func S) = t # ts\<close> by auto
        have B: "\<And> a . tv a = t \<Longrightarrow> 
          par_f (Rep_func S) (Rep_func T) (a # pref x ts @ suff x ts) = Some (the (Rep_func S (a # pref x ts)) @ the (Rep_func T (suff x ts)))"
          apply (simp add: par_f_def, safe)
          using A \<open>TI_f (Rep_func S) = t # ts\<close> apply auto[1]
          using \<open>TI_f (Rep_func S) = t # ts\<close> \<open>tp x = ts @ TI_f (Rep_func T)\<close> by auto

        have C: "(fb_t t (\<lambda>a. hd (the (par_f (Rep_func S) (Rep_func T) (a # x))))) = (fb_t t (\<lambda>a. hd (the (Rep_func S (a # pref x ts)))))"
          apply (rule fb_t_eq_type)
          apply (subst A)
          apply (simp add: B)
          apply (case_tac "the (Rep_func S (a # pref x ts))")
          apply simp_all
          proof -
            fix a :: Values
            assume a1: "tv a = t"
            assume a2: "the (Rep_func S (a # pref x ts)) = []"
            have f3: "tp (a # pref x ts) = t # ts"
              using a1 by (simp add: \<open>tp x = ts @ TI_f (Rep_func T)\<close>)
            have "tp (the (Rep_func S (a # pref x ts))) = []"
              using a2 by (metis tp.simps(1))
            then show "hd (the (Rep_func T (suff x ts))) = hd []"
              using f3 by (metis (no_types) \<open>TI_f (Rep_func S) = t # ts\<close> \<open>TO_f (Rep_func S) = t # ts'\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> has_type_out_type list.distinct(1))
          qed

       have "(pref (fb_t t (\<lambda>a. hd (the (Rep_func S (a # pref x ts)))) # x) (TI_f (Rep_func S))) 
            = (fb_t t (\<lambda>a. hd (the (Rep_func S (a # pref x ts)))) # pref x ts)"
            by (simp add: Ca)
          
      show " tl (the (par_f (Rep_func S) (Rep_func T) (fb_t t (\<lambda>a. hd (the (par_f (Rep_func S) (Rep_func T) (a # x)))) # x))) =
         tl (the (Rep_func S (fb_t t (\<lambda>a. hd (the (Rep_func S (a # pref x ts)))) # pref x ts))) @ the (Rep_func T (suff x ts))"
         apply (simp add: C)
         apply (simp add: par_f_def, auto)
         prefer 2 
         apply (simp add: \<open>TI_f (Rep_func S) = t # ts\<close> \<open>tp x = ts @ TI_f (Rep_func T)\<close>)
         apply (simp add: Ca)
         apply (case_tac "the (Rep_func S (fb_t t (\<lambda>a. hd (the (Rep_func S (a # pref x ts)))) # pref x ts))")
         apply (simp_all)
         apply (subgoal_tac "tp ((fb_t t (\<lambda>a. hd (the (Rep_func S (a # pref x ts)))) # pref x ts)) = t # ts")
         apply (metis Ca \<open>TO_f (Rep_func S) = t # ts'\<close> \<open>\<And>B. Rep_func B \<in> has_in_out_type (TI_f (Rep_func B)) (TO_f (Rep_func B))\<close> has_type_out_type list.distinct(1) tp.simps(1))
         by simp

     qed
     show "fb_func (Switch_func [t] [t]) = ID_func [t]"
      apply (simp add: TI_func_def fb_func_def TO_func_def Switch_func_def Abs_func_inverse Rep_func parallel_func_def ID_func_def comp_func_def)
      apply (subgoal_tac "(fb_f (Switch_f [t] [t])) = (ID_f [t])", simp_all)
      apply (simp add: fun_eq_iff Switch_f_def ID_f_def fb_f_def, auto)
      apply (case_tac x, simp_all, safe)
      proof -
        fix a
        assume "t = tv a"
      have "fb_t (tv a) (\<lambda>aa. hd (the (if tv aa = tv a then Some (suff [aa, a] [tv a] @ pref [aa, a] [tv a]) else None)))
        = fb_t (tv a) (\<lambda> aa . a)"
        apply (rule fb_t_eq_type)
        by simp
      from this show "fb_t (tv a) (\<lambda>aa. hd (the (if tv aa = tv a then Some (suff [aa, a] [tv a] @ pref [aa, a] [tv a]) else None))) = a"
        by simp
    qed
  qed
end