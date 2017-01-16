theory AbstractOperations imports ListProp
begin
  locale BaseOperation = 

    fixes TI TO :: "'a \<Rightarrow> 'tp list"


    fixes ID :: "'tp list \<Rightarrow> 'a"
    assumes [simp]: "TI(ID ts) = ts"
    assumes [simp]: "TO(ID ts) = ts"

    (*Serial*)
    fixes comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "oo" 70)
    assumes TI_comp[simp]: "TI S' = TO S \<Longrightarrow> TI (S oo S') = TI S"
    assumes TO_comp[simp]: "TI S' = TO S \<Longrightarrow> TO (S oo S') = TO S'"
    assumes comp_id_left [simp]: "ID (TI S) oo S  = S"
    assumes comp_id_right [simp]: "S oo ID (TO S) = S"
    assumes comp_assoc: "TI T = TO S \<Longrightarrow> TI R = TO T \<Longrightarrow> S oo T oo R = S oo (T oo R)"


    (*Parallel*)
    fixes parallel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<parallel>" 80)
    assumes TI_par [simp]: "TI (S \<parallel> T) = TI S @ TI T"
    assumes TO_par [simp]: "TO (S \<parallel> T) = TO S @ TO T"
    assumes par_assoc: "A \<parallel> B \<parallel> C = A \<parallel> (B \<parallel> C)"
    assumes empty_par[simp]: "ID [] \<parallel> S = S"
    assumes par_empty[simp]: "S \<parallel> ID [] = S" (*can be proved*)
    assumes parallel_ID [simp]: "ID ts \<parallel> ID ts' = ID (ts @ ts')"

    (*Comp Parallel*)
    assumes comp_parallel_distrib: "TO S = TI S' \<Longrightarrow> TO T = TI T' \<Longrightarrow> (S \<parallel> T) oo (S' \<parallel> T') = (S oo S') \<parallel> (T oo T')"

    (*Split Sink Switch axioms*)
    fixes Split    :: "'tp list \<Rightarrow> 'a"
    fixes Sink   :: "'tp list \<Rightarrow> 'a"
    fixes Switch :: "'tp list \<Rightarrow> 'tp list \<Rightarrow> 'a"

    assumes TI_Split[simp]: "TI (Split ts) = ts"
    assumes TO_Split[simp]: "TO (Split ts) = ts @ ts"

    assumes TI_Sink[simp]: "TI (Sink ts) = ts"
    assumes TO_Sink[simp]: "TO (Sink ts) = []"

    assumes TI_Switch[simp]: "TI (Switch ts ts') = ts @ ts'"
    assumes TO_Switch[simp]: "TO (Switch ts ts') = ts' @ ts"

    (*todo: check is these can be simplified*)
    assumes Split_Sink_id[simp]: "Split ts oo Sink ts \<parallel> ID ts = ID ts"
(*    assumes Split_id_Sink[simp]: "Split ts oo ID ts \<parallel> Sink ts = ID ts" can be proved*)
    assumes Split_Switch[simp]: "Split ts oo Switch ts ts = Split ts"
    assumes Split_assoc: "Split ts oo ID ts \<parallel> Split ts = Split ts oo Split ts \<parallel> ID ts"

    assumes Switch_append: "Switch ts (ts' @ ts'') = Switch ts ts' \<parallel> ID ts'' oo ID ts' \<parallel> Switch ts ts''"
    assumes Sink_append: "Sink ts \<parallel> Sink ts' = Sink (ts @ ts')"
    assumes Split_append: "Split (ts @ ts') = Split ts \<parallel> Split ts' oo ID ts \<parallel> Switch ts ts' \<parallel> ID ts'"


    (*Switch parallel*)
    assumes switch_par_no_vars: "TI A = ti \<Longrightarrow> TO A = to \<Longrightarrow> TI B = ti' \<Longrightarrow> TO B = to' \<Longrightarrow> Switch ti ti' oo B \<parallel> A oo Switch to' to = A \<parallel> B"


    (*feedback axioms*)
    fixes fb :: "'a \<Rightarrow> 'a"
    assumes TI_fb: "TI S = t # ts \<Longrightarrow> TO S = t # ts' \<Longrightarrow> TI (fb S) = ts" (*simp*)
    assumes TO_fb: "TI S = t # ts \<Longrightarrow> TO S = t # ts' \<Longrightarrow> TO (fb S) = ts'" (*simp*)
    assumes fb_comp: "TI S = t # TO A \<Longrightarrow> TO S = t # TI B \<Longrightarrow> fb (ID [t] \<parallel> A oo S oo ID [t] \<parallel> B) = A oo fb S oo B"
    assumes fb_par_indep: "TI S = t # ts \<Longrightarrow> TO S = t # ts' \<Longrightarrow> fb (S \<parallel> T) = fb S \<parallel> T"

    assumes fb_switch: "fb (Switch [t] [t]) = ID [t]"

    assumes fb_twice_switch_no_vars: "TI S = t' # t # ts \<Longrightarrow> TO S = t' # t # ts' 
      \<Longrightarrow> (fb ^^ (2::nat)) (Switch [t] [t'] \<parallel> ID ts oo S oo Switch [t'] [t] \<parallel> ID ts') = (fb ^^ (2:: nat)) S"

    begin

      definition "fbtype S tsa ts ts' = (TI S = tsa @ ts \<and> TO S = tsa @ ts')"

      lemma fb_comp_fbtype: "fbtype S [t] (TO A) (TI B) \<Longrightarrow> fb ((ID [t] \<parallel> A) oo S oo (ID [t] \<parallel> B)) = A oo fb S oo B"
        by (simp add: fbtype_def fb_comp)

      lemma fb_serial_no_vars: "TO A = t # ts \<Longrightarrow> TI B = t # ts \<Longrightarrow> fb ( ID [t] \<parallel> A oo Switch [t] [t] \<parallel> ID ts oo ID [t] \<parallel> B) = A oo B"
        apply (subst fb_comp)
        apply (simp_all)
        apply (subst fb_par_indep, simp_all)
        apply (simp add: fb_switch)
        by (metis comp_id_right)

      lemma TI_fb_fbtype: "fbtype S [t] ts ts' \<Longrightarrow> TI (fb S) = ts"
        by (simp add: fbtype_def TI_fb)
      lemma TO_fb_fbtype: "fbtype S [t] ts ts' \<Longrightarrow> TO (fb S) = ts'"
        by (simp add: fbtype_def TO_fb)
      lemma fb_par_indep_fbtype: "fbtype S [t] ts ts' \<Longrightarrow> fb (S \<parallel> T) = fb S \<parallel> T"
        by (simp add: fbtype_def fb_par_indep)

      lemma comp_id_left_simp [simp]: "TI S = ts \<Longrightarrow> ID ts oo S  = S"
        apply (cut_tac S = S in comp_id_left)
        by (simp del: comp_id_left)

      lemma comp_id_right_simp [simp]: "TO S = ts \<Longrightarrow> S oo ID ts = S"
        apply (cut_tac S = S in comp_id_right)
        by (simp del: comp_id_right)

      lemma par_Sink_comp: "TI A = TO B \<Longrightarrow> B \<parallel> Sink t oo A = (B oo A) \<parallel> Sink t"
        proof -
          assume [simp]: "TI A = TO B"

          have "B \<parallel> Sink t oo A = B \<parallel> Sink t oo A \<parallel> ID []"
            by simp          
          also have "... = (B oo A) \<parallel> Sink t"
            by (subst comp_parallel_distrib, simp_all)
          finally show ?thesis
            by simp
        qed

      lemma Sink_par_comp: "TI A = TO B \<Longrightarrow> Sink t \<parallel> B oo A = Sink t \<parallel> (B oo A)"
        proof -
          assume [simp]: "TI A = TO B"

          have "Sink t \<parallel> B oo A  = Sink t \<parallel> B oo ID [] \<parallel> A"
            by simp
          also have "... = Sink t \<parallel> (B oo A)"
            by (subst comp_parallel_distrib, simp_all)
          finally show ?thesis
            by simp
        qed

      lemma Split_Sink_par[simp]: "TI A = ts \<Longrightarrow> Split ts oo Sink ts \<parallel> A = A"
        proof -
          assume [simp]: "TI A = ts"
          have "Split ts oo Sink ts \<parallel> A = Split ts oo (Sink ts oo ID []) \<parallel> (ID (TI A) oo A)"
            by simp
          also have "... = Split ts oo Sink ts \<parallel> ID (TI A) oo A"
            by (subst comp_parallel_distrib[THEN sym], simp_all add: comp_assoc[THEN sym])
          also have "... = A"
            by simp
          finally show ?thesis
            by simp
        qed


      lemma Switch_Switch_ID[simp]: "Switch ts ts' oo Switch ts' ts = ID (ts @ ts')" 
        by (cut_tac A = "ID ts" and B = "ID ts'" in switch_par_no_vars, auto)

      lemma Switch_parallel: "TI A = ts' \<Longrightarrow> TI B = ts \<Longrightarrow> Switch ts ts' oo A \<parallel> B = B \<parallel> A oo Switch (TO B) (TO A)"
        proof -
          assume [simp]: "TI A = ts'" and [simp]: "TI B = ts"
          have "Switch ts ts' oo A \<parallel> B = Switch ts ts' oo A \<parallel> B oo Switch (TO A) (TO B) oo Switch (TO B) (TO A)"
            by (simp add: comp_assoc)
          also have "... = B \<parallel> A oo Switch (TO B) (TO A)"
            by (simp add: switch_par_no_vars)
          finally show ?thesis
            by simp
        qed


      lemma Switch_type_empty[simp]: "Switch ts [] = ID ts"
        by (metis Switch_Switch_ID Switch_append TI_Switch TO_Switch append_Nil empty_par par_empty switch_par_no_vars)

      lemma Switch_empty_type[simp]: "Switch [] ts = ID ts"
        by (metis Switch_Switch_ID Switch_type_empty TO_Switch append_Nil append_Nil2 comp_id_right_simp)

     lemma Split_id_Sink[simp]: "Split ts oo ID ts \<parallel> Sink ts = ID ts"
      proof - 
        have "Split ts oo ID ts \<parallel> Sink ts = Split ts oo (Switch ts ts oo  ID ts \<parallel> Sink ts)"
          by (simp add: comp_assoc [THEN sym])
        also have "... =ID ts"
          by (simp add: Switch_parallel)
        finally show ?thesis
          by simp
        qed

        
    lemma Split_par_Sink[simp]: "TI A = ts \<Longrightarrow> Split ts oo A \<parallel> Sink ts = A"
        proof -
          assume [simp]: "TI A = ts"
          have "Split ts oo A \<parallel> Sink ts = Split ts oo (ID (TI A) oo A) \<parallel> (Sink ts oo ID [])"
            by simp
          also have "... = Split ts oo  ID (TI A) \<parallel> Sink ts oo A"
            by (subst comp_parallel_distrib[THEN sym], simp_all add: comp_assoc[THEN sym])
          also have "... = A"
            by simp
          finally show ?thesis
            by simp
        qed
        
      lemma Split_empty [simp]: "Split [] = ID []"
        by (metis BaseOperation.par_empty BaseOperation_axioms Split_Sink_id Split_par_Sink Sink_append TI_Sink TO_Split append_is_Nil_conv comp_id_right)

      lemma Sink_empty[simp]: "Sink [] = ID []"
        by (metis Split_Sink_id Split_empty TI_Sink comp_id_left_simp par_empty)



      lemma Switch_Split: "Switch ts ts' = Split (ts @ ts') oo Sink ts \<parallel> ID ts' \<parallel> ID ts \<parallel> Sink ts'"
        proof - 
          have "Split (ts @ ts') oo Sink ts \<parallel> ID ts' \<parallel> ID ts \<parallel> Sink ts' = Split ts \<parallel> Split ts' oo (ID ts \<parallel> Switch ts ts' \<parallel> ID ts' oo Sink ts \<parallel> (ID ts' \<parallel> ID ts) \<parallel> Sink ts')"
            by (simp add: Split_append comp_assoc par_assoc del: parallel_ID)
          also have "... = Split ts \<parallel> Split ts' oo Sink ts \<parallel> Switch ts ts' \<parallel> Sink ts'"
            apply (subst comp_parallel_distrib)
            apply simp_all [2]
            by (subst (2) comp_parallel_distrib, simp_all)
          also have "... = Split ts \<parallel> Split ts' oo (Sink ts \<parallel> (ID ts \<parallel> ID ts') \<parallel> Sink ts' oo ID [] \<parallel> Switch ts ts' \<parallel> ID[])"
            apply (subst (2) comp_parallel_distrib)
            apply simp_all [2]
            apply (subst (3) comp_parallel_distrib)
            by simp_all
          also have "... =  Split ts \<parallel> Split ts' oo (Sink ts \<parallel> ID ts) \<parallel> (ID ts' \<parallel> Sink ts') oo Switch ts ts'"
            by (simp add: comp_assoc par_assoc del: parallel_ID)
          also have "... = Switch ts ts'"
            by (simp add: comp_parallel_distrib)
          finally show ?thesis
            by simp
        qed


      lemma Sink_cons: "Sink (t # ts) = Sink [t] \<parallel> Sink ts"
        by (simp add: Sink_append)

      lemma Split_cons: "Split (t # ts) = Split [t] \<parallel> Split ts oo ID [t] \<parallel> Switch [t] ts \<parallel> ID ts"
        by (simp add: Split_append [THEN sym])


      lemma Split_assoc_comp: "TI A = ts \<Longrightarrow> TI B = ts \<Longrightarrow> TI C = ts \<Longrightarrow> Split ts oo A \<parallel> (Split ts oo B \<parallel> C) = Split ts oo (Split ts oo A \<parallel> B) \<parallel> C"
        proof - 
          assume [simp]: "TI A = ts" and [simp]: "TI B = ts" and [simp]: "TI C = ts"
          have "Split ts oo A \<parallel> (Split ts oo B \<parallel> C) = Split ts oo ID ts \<parallel> Split ts oo A \<parallel> (B \<parallel> C)"
            by (simp add: comp_assoc comp_parallel_distrib)
          also have "... = Split ts oo (Split ts oo A \<parallel> B) \<parallel> C"
            by (subst Split_assoc, simp add: comp_assoc par_assoc [THEN sym] comp_parallel_distrib)
          finally show ?thesis by simp
        qed

      lemma Split_Split_Switch: "Split ts oo Split ts \<parallel> Split ts oo ID ts \<parallel> Switch ts ts \<parallel> ID ts = Split ts oo Split ts \<parallel> Split ts"
        proof -
          have "Split ts oo Split ts \<parallel> Split ts = Split ts oo Split ts \<parallel> (Split ts oo ID ts \<parallel> ID ts)"
            by simp
          also have "... = Split ts oo (Split ts oo Split ts \<parallel> ID ts) \<parallel> ID ts"
            by (subst Split_assoc_comp, simp_all)
          also have "... = Split ts oo (Split ts oo (Split ts oo ID ts \<parallel> ID ts) \<parallel> ID ts) \<parallel> ID ts"
            by (simp)
          also have "... = Split ts oo (Split ts oo ID ts \<parallel> Split ts) \<parallel> ID ts"
            by (subst (2) Split_assoc_comp[THEN sym], simp_all)
          finally have A: "Split ts oo Split ts \<parallel> Split ts = Split ts oo (Split ts oo ID ts \<parallel> Split ts) \<parallel> ID ts"
            by simp
          have "Split ts oo Split ts \<parallel> Split ts oo ID ts \<parallel> Switch ts ts \<parallel> ID ts = Split ts oo ((Split ts oo ID ts \<parallel> Split ts) \<parallel> ID ts oo ID ts \<parallel> Switch ts ts \<parallel> ID ts)"
            by (simp add: A comp_assoc)
          also have "... = Split ts oo (Split ts oo ID ts \<parallel> Split ts) \<parallel> ID ts"
            by (simp add: comp_parallel_distrib comp_assoc)
          also have "... =  Split ts oo Split ts \<parallel> Split ts"
            by (simp add: A)
          finally show ?thesis by simp
        qed
        
      lemma parallel_empty_commute: "TI A = [] \<Longrightarrow> TO B = [] \<Longrightarrow> A \<parallel> B = B \<parallel> A"
        proof -
        assume [simp]: "TI A = []" and [simp]: "TO B = []"
        have "A \<parallel> B = Switch (TI B) [] oo A \<parallel> B"
          by simp
        also have "... = B \<parallel> A"
          by (subst Switch_parallel, simp_all)
        finally show ?thesis by simp
        qed

      definition "deterministic S = (Split (TI S) oo S \<parallel> S = S oo Split (TO S))"

    end


  locale BaseOperationVars = BaseOperation +
    fixes TV :: "'var \<Rightarrow> 'b"
    fixes newvar :: "'var list \<Rightarrow> 'b \<Rightarrow> 'var"
    assumes newvar_type[simp]: "TV(newvar x t) = t"
    assumes newvar_distinct [simp]: "newvar x t \<notin> set x"
    assumes "ID [TV a] = ID [TV a]"
  begin
    primrec TVs::"'var list \<Rightarrow> 'b list" where
      "TVs [] = []" |
      "TVs (a # x) = TV a # TVs x"

    lemma TVs_append: "TVs (x @ y) = TVs x @ TVs y"
      by (induction x, simp_all)
      
    definition "Arb t = fb (Split [t])"
      
    lemma TI_Arb[simp]: "TI (Arb t) = []"
      by (simp add: TI_fb Arb_def)

    lemma TO_Arb[simp]: "TO (Arb t) = [t]"
      by (simp add: TO_fb Arb_def)

    fun set_var:: "'var list \<Rightarrow> 'var \<Rightarrow> 'a" where
      "set_var [] b = Arb (TV b)" |
      "set_var (a # x) b = (if a = b then ID [TV a] \<parallel> Sink (TVs x) else Sink [TV a] \<parallel> set_var x b)" 
       
    lemma TO_set_var[simp]: "TO (set_var x a) = [TV a]"
      by (induction x, simp_all)
      
    lemma TI_set_var[simp]: "TI (set_var x a) = TVs x"
      by (induction x, simp_all)

    primrec switch :: "'var list \<Rightarrow> 'var list \<Rightarrow> 'a" ("[_ \<leadsto> _]") where
      "[x \<leadsto> []] = Sink (TVs x)" |
      "[x \<leadsto> a # y] = Split (TVs x) oo set_var x a \<parallel> [x \<leadsto> y]"

    lemma TI_switch[simp]: "TI [x \<leadsto> y] = TVs x"
      by (induction y, simp_all)

    lemma TO_switch[simp]: " TO [x \<leadsto> y] = TVs y"
      by (induction y, simp_all)

    lemma switch_not_in_Sink: "a \<notin> set y \<Longrightarrow>  [a # x \<leadsto> y] = Sink [TV a] \<parallel> [x \<leadsto> y]"
      proof (induction y)
        case Nil
        show ?case by (simp add: Sink_append)
        next
        case (Cons b y)
          thm Cons

        have [simp]: "a \<noteq> b"
          using Cons by simp
        have [simp]: "a \<notin> set y"
          using Cons by simp
        thm Split_append
        have "Split (TV a # TVs x) oo Sink [TV a] \<parallel> set_var x b \<parallel> (Sink [TV a] \<parallel> [x \<leadsto> y]) 
          = Split [TV a] \<parallel> Split (TVs x) oo ID [TV a] \<parallel> Switch [TV a] (TVs x) \<parallel> ID (TVs x) oo Sink [TV a] \<parallel> set_var x b \<parallel> (Sink [TV a] \<parallel> [x \<leadsto> y])"
          by (subst Split_cons, simp)
        also have "...= Split [TV a] \<parallel> Split (TVs x) oo (ID [TV a] \<parallel> Switch [TV a] (TVs x) \<parallel> ID (TVs x) oo Sink [TV a] \<parallel> (set_var x b \<parallel> Sink [TV a]) \<parallel> [x \<leadsto> y])"
          by (simp add: par_assoc comp_assoc)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo Sink [TV a] \<parallel> (Switch [TV a] (TVs x) oo set_var x b \<parallel> Sink [TV a]) \<parallel> [x \<leadsto> y]"
          by (simp add: comp_parallel_distrib)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo Sink [TV a] \<parallel> (Sink [TV a] \<parallel> set_var x b) \<parallel> [x \<leadsto> y]"
          by (subst Switch_parallel, simp_all)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo (Sink [TV a] \<parallel> Sink [TV a]) \<parallel> (set_var x b \<parallel> [x \<leadsto> y])"
          by (simp add: par_assoc)
        also have "... = Sink [TV a] \<parallel> (Split (TVs x) oo set_var x b \<parallel> [x \<leadsto> y])"
          by (simp add: comp_parallel_distrib)
        finally show ?case
          using Cons by simp
      qed

    lemma distinct_id: "distinct x \<Longrightarrow> [x \<leadsto> x] = ID (TVs x)"
      proof (induction x)

      case Nil
      show ?case
        by simp
      next
      case (Cons a x)
        have " Split (TV a # TVs x) oo ID [TV a] \<parallel> Sink (TVs x) \<parallel> (Sink [TV a] \<parallel> ID (TVs x)) 
          = Split [TV a] \<parallel> Split (TVs x) oo ID [TV a] \<parallel> Switch [TV a] (TVs x) \<parallel> ID (TVs x) oo ID [TV a] \<parallel> Sink (TVs x) \<parallel> (Sink [TV a] \<parallel> ID (TVs x))"
          by (subst Split_cons, simp)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo (ID [TV a] \<parallel> Switch [TV a] (TVs x) \<parallel> ID (TVs x) oo ID [TV a] \<parallel> (Sink (TVs x) \<parallel> Sink [TV a]) \<parallel> ID (TVs x))"
          by (simp add: comp_assoc par_assoc)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo (ID [TV a] \<parallel> (Switch [TV a] (TVs x) oo Sink (TVs x) \<parallel> Sink [TV a]) \<parallel> ID (TVs x))"
          by (simp add: comp_parallel_distrib)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo ID [TV a] \<parallel> (Sink [TV a] \<parallel> Sink (TVs x)) \<parallel> ID (TVs x)"
          by (subst Switch_parallel, simp_all)
        also have "... = Split [TV a] \<parallel> Split (TVs x) oo (ID [TV a] \<parallel> Sink [TV a]) \<parallel> (Sink (TVs x) \<parallel> ID (TVs x))"
          by (simp add: par_assoc)
        also have "... = ID [TV a] \<parallel> ID (TVs x)"
          by (simp add: comp_parallel_distrib)
      finally show ?case
        using Cons by (simp add: switch_not_in_Sink)
      qed

      lemma set_var_nin: "a \<notin> set x \<Longrightarrow> set_var (x @ y) a = Sink (TVs x) \<parallel> set_var y a"
        by (induction x, simp_all, auto simp add: par_assoc [THEN sym] Sink_append)

      lemma set_var_in: "a \<in> set x \<Longrightarrow> set_var (x @ y) a = set_var x a \<parallel> Sink (TVs y)"
        by (induction x, simp_all, auto simp add: par_assoc Sink_append TVs_append)
        
      

      lemma set_var_not_in: "a \<notin> set y \<Longrightarrow> set_var y a = Arb (TV a) \<parallel> Sink (TVs y)"
        apply (induction y, simp_all, auto)
        apply (simp add: par_assoc [THEN sym])
        apply (subst parallel_empty_commute [THEN sym], simp_all)
        by (subst (2) Sink_cons, simp add: par_assoc)

      lemma set_var_in_a: "a \<notin> set y \<Longrightarrow> set_var (x @ y) a = set_var x a \<parallel> Sink (TVs y)"
        by (induction x, simp_all, auto simp add: par_assoc Sink_append TVs_append set_var_not_in)

      lemma switch_append: "[x \<leadsto> y @ z] = Split (TVs x) oo [x \<leadsto> y] \<parallel> [x \<leadsto> z]"
        by (induction y, simp_all add: Split_assoc_comp switch_not_in_Sink)

     lemma switch_nin_a_new: "set x \<inter> set y' = {} \<Longrightarrow> [x @ y \<leadsto> y'] = Sink (TVs x) \<parallel> [y \<leadsto> y']"
      proof (induction y')
        case Nil
        show ?case by (simp add: Sink_append TVs_append)
        next
        case (Cons a y')
        have [simp]: "a \<notin> set x"
          using Cons by simp
        have [simp]: "set x \<inter> set y' = {}"
          using Cons by simp

        have "Split (TVs x) \<parallel> Split (TVs y) oo ID (TVs x) \<parallel> Switch (TVs x) (TVs y) \<parallel> ID (TVs y) oo Sink (TVs x) \<parallel> set_var y a \<parallel> (Sink (TVs x) \<parallel> [y \<leadsto> y'])
          = Split (TVs x) \<parallel> Split (TVs y) oo (ID (TVs x) \<parallel> Switch (TVs x) (TVs y) \<parallel> ID (TVs y) oo Sink (TVs x) \<parallel> (set_var y a \<parallel> Sink (TVs x)) \<parallel> [y \<leadsto> y'])"
          by (simp add: comp_assoc par_assoc)
        also have "... = Split (TVs x) \<parallel> Split (TVs y) oo Sink (TVs x) \<parallel> Sink (TVs x) \<parallel> set_var y a \<parallel> [y \<leadsto> y']"
          apply (simp add: comp_parallel_distrib Switch_parallel )
          by (simp add: par_assoc)
        also have "... = Split (TVs x) \<parallel> Split (TVs y) oo (Sink (TVs x) \<parallel> Sink (TVs x)) \<parallel> (set_var y a \<parallel> [y \<leadsto> y'])"
          by (simp only: par_assoc)

        also have "... = Sink (TVs x) \<parallel> (Split (TVs y) oo set_var y a \<parallel> [y \<leadsto> y'])"
          by (simp add: comp_parallel_distrib)

        finally show ?case
          using Cons by (simp add: Sink_append set_var_nin TVs_append Split_append)
      qed

    lemma switch_nin_b_new: "set y \<inter> set z = {} \<Longrightarrow> [x @ y \<leadsto> z] = [x \<leadsto> z] \<parallel> Sink (TVs y)"
      proof (induction z)
      case Nil
      show ?case by (simp add: TVs_append Sink_append)
      next
      case (Cons a z)
      have [simp]: "a \<notin> set y" and [simp]: "set y \<inter> set z = {}"
      using Cons by simp_all
      have "Split (TVs (x @ y)) oo set_var (x @ y) a \<parallel> ([x \<leadsto> z] \<parallel> Sink (TVs y)) 
        = Split (TVs x) \<parallel> Split (TVs y) oo (ID (TVs x) \<parallel> Switch (TVs x) (TVs y) \<parallel> ID (TVs y) oo set_var x a \<parallel> (Sink (TVs y) \<parallel> [x \<leadsto> z]) \<parallel> Sink (TVs y))"
        by (simp add: Split_append TVs_append set_var_in par_assoc comp_assoc set_var_in_a)
      also have "... = Split (TVs x) \<parallel> Split (TVs y) oo set_var x a \<parallel> [x \<leadsto> z] \<parallel> Sink (TVs y) \<parallel> Sink (TVs y)"
        apply (simp add: comp_parallel_distrib Switch_parallel)
        by (simp add: par_assoc)
      also have "... =  Split (TVs x) \<parallel> Split (TVs y) oo (set_var x a \<parallel> [x \<leadsto> z]) \<parallel> (Sink (TVs y) \<parallel> Sink (TVs y))"
        by (simp add: par_assoc)
      also have "... =  (Split (TVs x) oo set_var x a \<parallel> [x \<leadsto> z]) \<parallel> Sink (TVs y)"
        by (simp add: comp_parallel_distrib)
      finally show ?case
      using Cons by simp
     qed


     lemma var_switch: "distinct (x @ y) \<Longrightarrow> [x @ y \<leadsto> y @ x] = Switch (TVs x) (TVs y)"
      proof -
        assume "distinct (x @ y)"
        from this have [simp]: "distinct x" and [simp]: "distinct y" and [simp]: "set x \<inter> set y = {}" and [simp]: "set y \<inter> set x = {}"
          by auto
        have "[x @ y \<leadsto> y @ x] = Split (TVs x) \<parallel> Split (TVs y) oo (ID (TVs x) \<parallel> Switch (TVs x) (TVs y) \<parallel> ID (TVs y) oo Sink (TVs x) \<parallel> (ID (TVs y) \<parallel> ID (TVs x)) \<parallel> Sink (TVs y))"
          by (simp add: switch_append switch_nin_a_new switch_nin_b_new distinct_id TVs_append Split_append par_assoc comp_assoc del: parallel_ID)
        also have "... = Split (TVs x) \<parallel> Split (TVs y) oo Sink (TVs x) \<parallel> Switch (TVs x) (TVs y) \<parallel> Sink (TVs y)"
          by (simp add: comp_parallel_distrib)

        thm comp_parallel_distrib

        also have "... = Split (TVs x) \<parallel> Split (TVs y) oo (Sink (TVs x) \<parallel> (ID (TVs x) \<parallel> ID (TVs y)) \<parallel> Sink (TVs y) oo ID [] \<parallel> Switch (TVs x) (TVs y) \<parallel> ID [])"
          apply (subst (2) comp_parallel_distrib)
          apply simp_all [2]
          apply (subst (3) comp_parallel_distrib)
          by (simp_all)

        also have "... = Split (TVs x) \<parallel> Split (TVs y) oo (Sink (TVs x) \<parallel> ID (TVs x)) \<parallel> (ID (TVs y) \<parallel> Sink (TVs y)) oo Switch (TVs x) (TVs y)"
          by (unfold par_assoc, simp add: comp_assoc)
        also have "... = Switch (TVs x) (TVs y)"
          by (subst comp_parallel_distrib, simp_all)
       finally show ?thesis by simp
     qed

    lemma  switch_par: "distinct (x @ y) \<Longrightarrow> distinct (u @ v) \<Longrightarrow> TI S = TVs x \<Longrightarrow> TI T = TVs y \<Longrightarrow> TO S = TVs v \<Longrightarrow> TO T = TVs u \<Longrightarrow> 
      S \<parallel> T = [x @ y \<leadsto> y @ x] oo T \<parallel> S oo [u @ v \<leadsto> v @ u]"
      by (simp add: var_switch switch_par_no_vars)


    lemma par_switch: "distinct (x @ y) \<Longrightarrow> set x' \<subseteq> set x \<Longrightarrow> set y' \<subseteq> set y \<Longrightarrow>  [x \<leadsto> x'] \<parallel> [y \<leadsto> y'] = [x @ y \<leadsto> x' @ y']"
      proof -
        assume "distinct (x @ y)"
        from this have [simp]: "distinct x" and [simp]: "distinct y" and C: "set x \<inter> set y = {}" and "set y \<inter> set x = {}"
          by auto
        assume A: "set x' \<subseteq> set x"
        assume B: "set y' \<subseteq> set y"
        have "[x @ y \<leadsto> x' @ y'] 
          = Split (TVs x) \<parallel> Split (TVs y) oo (ID (TVs x) \<parallel> Switch (TVs x) (TVs y) \<parallel> ID (TVs y) oo [x \<leadsto> x'] \<parallel> (Sink (TVs y) \<parallel> Sink (TVs x)) \<parallel> [y \<leadsto> y'])"
          using A B apply (subst switch_append, auto)
          using C apply (subst switch_nin_b_new, auto)
          apply (subst switch_nin_a_new, auto)
          by (simp add: Split_append TVs_append comp_assoc par_assoc)
        also have "... = Split (TVs x) \<parallel> Split (TVs y) oo ([x \<leadsto> x'] \<parallel> Sink (TVs x)) \<parallel> (Sink (TVs y) \<parallel> [y \<leadsto> y'])"
          using A B apply (subst comp_parallel_distrib)
          apply simp_all [2]
          by (subst (2) comp_parallel_distrib, simp_all add: Switch_parallel par_assoc)
        also have "... = [x \<leadsto> x'] \<parallel> [y \<leadsto> y']"
          using A B by (simp add: comp_parallel_distrib)
        finally show ?thesis
          by simp
      qed


    lemma set_var_sink[simp]: "a \<in> set x \<Longrightarrow> (TV a) = t \<Longrightarrow> set_var x a oo Sink [t] = Sink (TVs x)"
      by (induction x, auto simp add: par_Sink_comp Sink_par_comp Sink_append)

    lemma switch_Sink[simp]: "\<And> ts . set u \<subseteq> set x \<Longrightarrow> TVs u = ts \<Longrightarrow> [x \<leadsto> u] oo Sink ts = Sink (TVs x)"
      apply (induction u, simp_all)
      apply (case_tac ts, simp_all)
      apply (subst Sink_cons)
      apply (subst comp_assoc, simp_all)
      by (simp add: comp_parallel_distrib)

    lemma set_var_dup: "a \<in> set x \<Longrightarrow> TV a = t \<Longrightarrow> set_var x a oo Split [t] = Split (TVs x) oo set_var x a  \<parallel> set_var x a"
      proof (induction x)
        case Nil
        from Nil show ?case by simp
        next
        case (Cons b x)

        have "Split (TV b # TVs x) oo ID [TV b] \<parallel> (Sink (TVs x) \<parallel> (ID [TV b] \<parallel> Sink (TVs x))) 
          = Split [TV b] \<parallel> Split (TVs x) oo (ID [TV b] \<parallel> Switch [TV b] (TVs x) \<parallel> ID (TVs x) oo ID [TV b] \<parallel> (Sink (TVs x) \<parallel> ID [TV b]) \<parallel> Sink (TVs x))"
          by (subst Split_cons, simp add: par_assoc comp_assoc)
        also have "... = Split [TV b] \<parallel> Split (TVs x) oo (ID [TV b] \<parallel> ID [TV b]) \<parallel> (Sink (TVs x) \<parallel> Sink (TVs x))"
          apply (subst comp_parallel_distrib)
          apply (simp_all) [2]
          apply (subst (2) comp_parallel_distrib)
          by (simp_all add: Switch_parallel par_assoc del: parallel_ID) 
        also have "... = Split [TV b] \<parallel> Sink (TVs x)"
          by (subst comp_parallel_distrib, simp_all)
        also have "... =  ID [TV b] \<parallel> Sink (TVs x) oo Split [TV b]"
          by (simp add: par_Sink_comp)
        finally have [simp]: "Split (TV b # TVs x) oo ID [TV b] \<parallel> (Sink (TVs x) \<parallel> (ID [TV b] \<parallel> Sink (TVs x))) = ID [TV b] \<parallel> Sink (TVs x) oo Split [TV b]"
          by simp

        have [simp]: "a = b \<Longrightarrow> ID [TV a] \<parallel> Sink (TVs x) oo Split [TV a] = Split (TV a # TVs x) oo ID [TV a] \<parallel> (Sink (TVs x) \<parallel> (ID [TV a] \<parallel> Sink (TVs x)))"
          by simp

        from Cons have "a \<in> set x \<Longrightarrow> set_var x a oo Split [TV a] = Split (TVs x) oo set_var x a \<parallel> set_var x a"
          by simp


        have "\<And> A . TI A = TVs x \<Longrightarrow> Split (TV b # TVs x) oo Sink [TV b] \<parallel> (A \<parallel> (Sink [TV b] \<parallel> A)) 
          = Split [TV b] \<parallel> Split (TVs x) oo (ID [TV b] \<parallel> Switch [TV b] (TVs x) \<parallel> ID (TVs x) oo Sink [TV b] \<parallel> (A \<parallel> Sink [TV b]) \<parallel> A)" 
          by (subst Split_cons, simp add: comp_assoc par_assoc) 
        also have "\<And> A . TI A = TVs x \<Longrightarrow>  Split [TV b] \<parallel> Split (TVs x) oo (ID [TV b] \<parallel> Switch [TV b] (TVs x) \<parallel> ID (TVs x) oo Sink [TV b] \<parallel> (A \<parallel> Sink [TV b]) \<parallel> A) 
          = Split [TV b] \<parallel> Split (TVs x) oo (Sink [TV b] \<parallel> Sink [TV b]) \<parallel> (A \<parallel> A)"
          apply (subst comp_parallel_distrib)
          apply (simp_all) [2]
          apply (subst (2) comp_parallel_distrib)
          by (simp_all add: Switch_parallel par_assoc) 
        also have "\<And> A . TI A = TVs x \<Longrightarrow>  Split [TV b] \<parallel> Split (TVs x) oo (Sink [TV b] \<parallel> Sink [TV b]) \<parallel> (A \<parallel> A)
          = Sink [TV b] \<parallel> (Split (TVs x) oo A \<parallel> A)"
          by (simp add: comp_parallel_distrib)
        finally have [simp]: "\<And> A . TI A = TVs x \<Longrightarrow> Split (TV b # TVs x) oo Sink [TV b] \<parallel> (A \<parallel> (Sink [TV b] \<parallel> A)) = Sink [TV b] \<parallel> (Split (TVs x) oo A \<parallel> A)"
          by simp
        show ?case
          using Cons apply (auto simp add: par_assoc comp_assoc )
          by (simp add: Sink_par_comp)
      qed

    lemma switch_dup: "\<And> ts . set y \<subseteq> set x \<Longrightarrow> TVs y = ts \<Longrightarrow> [x \<leadsto> y] oo Split ts = Split (TVs x) oo [x \<leadsto> y] \<parallel> [x \<leadsto> y]"
      proof (induction y)
      case Nil
      show ?case 
        using Nil by simp
      next
      case (Cons a y)

      obtain t ts' where [simp]: "ts = t # ts'" and [simp]: "TV a = t" and [simp]: "TVs y = ts'"
        using Cons by (case_tac ts, simp_all)

      have [simp]: "a \<in> set x"
        using Cons by simp
      have [simp]: "set y \<subseteq> set x"
        using Cons by simp

      have "Split (TVs x) oo set_var x a \<parallel> [x \<leadsto> y] oo Split (t # ts') 
        = Split (TVs x) oo set_var x a \<parallel> [x \<leadsto> y] oo (Split [t] \<parallel> Split ts' oo ID [t] \<parallel> Switch [t] ts' \<parallel> ID ts')"
        by (subst Split_cons, simp)

      also have "... = Split (TVs x) oo (set_var x a \<parallel> [x \<leadsto> y] oo Split [t] \<parallel> Split ts') oo ID [t] \<parallel> Switch [t] ts' \<parallel> ID ts'"
        by (simp add: comp_assoc)

      also have "... = Split (TVs x) oo (set_var x a oo Split [t]) \<parallel> ([x \<leadsto> y] oo Split ts') oo ID [t] \<parallel> Switch [t] ts' \<parallel> ID ts'"
        by (simp add: comp_parallel_distrib)

      also have "... = Split (TVs x) oo (Split (TVs x) oo set_var x a \<parallel> set_var x a) \<parallel> (Split (TVs x) oo [x \<leadsto> y] \<parallel> [x \<leadsto> y]) oo ID [t] \<parallel> Switch [t] ts' \<parallel> ID ts'"
        apply (simp add: set_var_dup)
        using Cons by simp

      also have "... = Split (TVs x) oo Split (TVs x) \<parallel> Split (TVs x) oo (set_var x a \<parallel> (set_var x a \<parallel> [x \<leadsto> y]) \<parallel> [x \<leadsto> y] oo ID [t] \<parallel> Switch [t] ts' \<parallel> ID ts')"
        by (subst comp_parallel_distrib [THEN sym], simp_all add: comp_assoc par_assoc)

      also have "... = Split (TVs x) oo Split (TVs x) \<parallel> Split (TVs x) oo set_var x a \<parallel> ( Switch (TVs x) (TVs x) oo [x \<leadsto> y] \<parallel> set_var x a) \<parallel> [x \<leadsto> y]"
        apply (simp add: comp_parallel_distrib)
        by (cut_tac A = "[x \<leadsto> y]" and B = " set_var x a" in Switch_parallel, simp_all, auto)

      also have "... = Split (TVs x) oo Split (TVs x) \<parallel> Split (TVs x) oo (ID (TVs x) \<parallel> Switch (TVs x) (TVs x) \<parallel> ID (TVs x) oo set_var x a \<parallel> ([x \<leadsto> y] \<parallel> set_var x a) \<parallel> [x \<leadsto> y])"
        by (simp add: comp_parallel_distrib)

      also have "... = Split (TVs x) oo Split (TVs x) \<parallel> Split (TVs x) oo set_var x a \<parallel> ([x \<leadsto> y] \<parallel> set_var x a) \<parallel> [x \<leadsto> y]"
        by (simp add: comp_assoc [THEN sym] Split_Split_Switch)

      also have "... =  Split (TVs x) oo (Split (TVs x) oo set_var x a \<parallel> [x \<leadsto> y]) \<parallel> (Split (TVs x) oo set_var x a \<parallel> [x \<leadsto> y])"
        by (simp add: comp_parallel_distrib[THEN sym] comp_assoc par_assoc)

      finally show ?case
        using Cons by simp
    qed

    lemma TVs_length_eq: "\<And> y . TVs x = TVs y \<Longrightarrow> length x = length y"
      apply (induction x)
      apply (case_tac y, simp)
      apply simp
      apply (case_tac y)
      apply (metis TVs.simps(1) TVs.simps(2) list.distinct(1))
      by simp      

    lemma set_var_comp_subst: "\<And> y . set u \<subseteq> set x \<Longrightarrow> TVs u = TVs y  \<Longrightarrow> a \<in> set y \<Longrightarrow> [x \<leadsto> u] oo set_var y a = set_var x (subst y u a)"
      apply (induction u, simp_all)
      apply (case_tac y, simp_all)
      apply (case_tac y, simp_all, auto)
      by (simp_all add: comp_assoc comp_parallel_distrib)  

    lemma switch_comp_subst: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set u \<subseteq> set x \<Longrightarrow> set v \<subseteq> set y \<Longrightarrow> TVs u = TVs y  \<Longrightarrow> [x \<leadsto> u] oo [y \<leadsto> v] = [x \<leadsto> Subst y u v]"
      apply (induction v, simp_all)
      apply (simp add: comp_assoc [THEN sym])
      apply (subst switch_dup, simp_all)
      by (simp add: comp_assoc comp_parallel_distrib set_var_comp_subst)

    declare switch.simps [simp del]

    lemma sw_hd_var: "distinct (a # b # x) \<Longrightarrow> [a # b # x \<leadsto> b # a # x] = Switch [TV a] [TV b] \<parallel> ID (TVs x)"
      apply (subgoal_tac "[a # b # x \<leadsto> b # a # x] = [[a,b]\<leadsto> [b,a]] \<parallel> [x \<leadsto> x]")
      apply (simp add: distinct_id)
      apply (cut_tac x = "[a]" and y = "[b]" in var_switch, simp_all)
      by (subst par_switch, simp_all)


    lemma fb_serial: "distinct (a # b # x) \<Longrightarrow> TV a = TV b \<Longrightarrow> TO A = TVs (b # x) \<Longrightarrow> TI B = TVs (a # x)\<Longrightarrow> fb (([[a] \<leadsto> [a]] \<parallel> A) oo [a # b # x \<leadsto> b # a # x] oo ([[b] \<leadsto> [b]] \<parallel> B)) = A oo B"
      by (cut_tac A = A and B = B and t = "TV a" and ts = "TVs x" in fb_serial_no_vars, simp_all add: distinct_id sw_hd_var)


    thm fb_twice_switch_no_vars
  
    lemma fb_twice_switch: "distinct (a # b # x) \<Longrightarrow> distinct (a # b # y) \<Longrightarrow> TI S = TVs (b # a # x) \<Longrightarrow> TO S = TVs (b # a # y) 
      \<Longrightarrow> (fb ^^ (2::nat)) ([a # b # x \<leadsto> b # a # x] oo S oo [b # a # y \<leadsto> a # b # y]) = (fb ^^ (2:: nat)) S"
      apply (cut_tac S = S  and t = "TV a" and t' = "TV b" and ts = "TVs x" in fb_twice_switch_no_vars, simp_all add: distinct_id sw_hd_var)
      by (subst sw_hd_var, auto)

    lemma Switch_Split: "distinct x \<Longrightarrow>  [x \<leadsto> x @ x] = Split (TVs x)"
      by (simp add: distinct_id switch_append)

  end
end
