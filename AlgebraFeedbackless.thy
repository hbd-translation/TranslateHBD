section{*Abstract Algebra of  Hierarchical Block Diagrams (except one axiom for feedback)*}

theory AlgebraFeedbackless imports ListProp
begin
  
locale BaseOperationFeedbackless =   
  (*Input output types*)
  fixes TI TO :: "'a \<Rightarrow> 'tp list"

  (*Identity*)
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

begin
definition "fbtype S tsa ts ts' = (TI S = tsa @ ts \<and> TO S = tsa @ ts')"

lemma fb_comp_fbtype: "fbtype S [t] (TO A) (TI B) 
  \<Longrightarrow> fb ((ID [t] \<parallel> A) oo S oo (ID [t] \<parallel> B)) = A oo fb S oo B"
  by (simp add: fbtype_def fb_comp)

lemma fb_serial_no_vars: "TO A = t # ts \<Longrightarrow> TI B = t # ts 
  \<Longrightarrow> fb ( ID [t] \<parallel> A oo Switch [t] [t] \<parallel> ID ts oo ID [t] \<parallel> B) = A oo B"
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
        by (metis par_empty Split_Sink_id Split_par_Sink Sink_append TI_Sink TO_Split append_is_Nil_conv comp_id_right)

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

    lemma comp_assoc_middle_ext: "TI S2 = TO S1 \<Longrightarrow> TI S3 = TO S2 \<Longrightarrow> TI S4 = TO S3 \<Longrightarrow> TI S5 = TO S4 \<Longrightarrow>
          S1 oo (S2 oo S3 oo S4) oo S5 = (S1 oo S2) oo S3 oo (S4 oo S5)"
        by (simp add: comp_assoc)

        lemma fb_gen_parallel: "\<And> S . fbtype S tsa ts ts' \<Longrightarrow> (fb^^(length tsa)) (S \<parallel> T) = ((fb^^(length tsa)) (S)) \<parallel> T"
          apply (induction tsa, simp_all)
          apply (simp add: funpow_swap1)
          apply (subst fb_par_indep_fbtype)
          apply (simp add:  fbtype_def)
          apply (subgoal_tac "fbtype (fb S) tsa ts ts'")
          apply simp
          apply (simp add: fbtype_def, safe)
          apply (rule TI_fb_fbtype, simp add: fbtype_def)
          by (rule TO_fb_fbtype, simp add: fbtype_def)
            
        lemmas parallel_ID_sym = parallel_ID [THEN sym]
        declare parallel_ID [simp del]

        lemma fb_indep: "\<And>S. fbtype S tsa (TO A) (TI B) \<Longrightarrow> (fb^^(length tsa)) ((ID tsa \<parallel> A) oo S oo (ID tsa \<parallel> B)) = A oo (fb^^(length tsa)) S oo B"   
          apply (induction tsa, simp_all)
          apply (simp add: funpow_swap1)
          apply (cut_tac ts="[a]" and ts'=tsa in parallel_ID_sym)
          apply (simp add: par_assoc)
          apply (subst fb_comp_fbtype)
          apply (simp add: fbtype_def)
          apply (subgoal_tac "fbtype (fb S) tsa (TO A) (TI B)")
          apply simp
          apply (simp add: fbtype_def, safe)
          apply (rule TI_fb_fbtype, simp add: fbtype_def)
          by (rule TO_fb_fbtype, simp add: fbtype_def)

        lemma fb_indep_a: "\<And>S. fbtype S tsa (TO A) (TI B) \<Longrightarrow> length tsa = n \<Longrightarrow> (fb ^^ n) ((ID tsa \<parallel> A) oo S oo (ID tsa \<parallel> B)) = A oo (fb ^^ n) S oo B"
          by (drule fb_indep, simp_all)

        lemma fb_comp_right: "fbtype S [t] ts (TI B) \<Longrightarrow> fb (S oo (ID [t] \<parallel> B)) = fb S oo B"
          proof -
            assume [simp]: "fbtype S [t] ts (TI B)"
            have "fb (S oo (ID [t] \<parallel> B)) = fb (ID (t#ts) oo S oo (ID [t] \<parallel> B))"
              apply (subst comp_id_left_simp)
              apply simp_all
              apply (subgoal_tac "fbtype S [t] ts (TI B)")
              apply (simp add: fbtype_def)
              by simp
            also have "... = fb (ID ([t]) \<parallel> ID ts oo S oo (ID [t] \<parallel> B))"
              apply (cut_tac ts="[t]" and ts'="ts" in parallel_ID_sym)
              by simp
            also have "... = ID ts oo fb S oo B"
              apply (rule fb_comp_fbtype)
              by simp
            also have "... = fb S oo B"
              apply (subst comp_id_left_simp)
              apply simp_all
              apply (subgoal_tac "fbtype S [t] ts (TI B)")
              apply (simp only: TI_fb_fbtype)
              by simp
            finally show "fb (S oo (ID [t] \<parallel> B)) = fb S oo B"
              by simp
          qed

        lemma fb_comp_left: "fbtype S [t] (TO A) ts \<Longrightarrow> fb ((ID [t] \<parallel> A) oo S) = A oo fb S"
          proof -
            assume [simp]: "fbtype S [t] (TO A) ts"
            have "fb ((ID [t] \<parallel> A) oo S) = fb ((ID [t] \<parallel> A) oo S oo ID (t#ts))"
              apply (subst comp_id_right_simp)
              apply simp_all
              apply (subgoal_tac "fbtype S [t] (TO A) ts")
              apply (subst TO_comp)
              apply (simp add: fbtype_def)
              apply (simp add: fbtype_def)
              by simp
            also have "... = fb (ID ([t]) \<parallel> A oo S oo (ID [t] \<parallel> ID ts))"
              apply (cut_tac ts="[t]" and ts'="ts" in parallel_ID)
              by simp
            also have "... = A oo fb S oo ID ts"
              apply (rule fb_comp_fbtype)
              by simp
            also have "... = A oo fb S"
              apply (subst comp_id_right_simp)
              apply simp_all
              apply (subgoal_tac "fbtype S [t] (TO A) ts")
              apply (subst TO_comp)
              apply (simp only: TI_fb_fbtype)
              apply (simp only: TO_fb_fbtype)
              by simp
            finally show "fb ((ID [t] \<parallel> A) oo S) = A oo fb S"
              by simp
          qed

        lemma fb_indep_right: "\<And>S. fbtype S tsa ts (TI B) \<Longrightarrow> (fb^^(length tsa)) (S oo (ID tsa \<parallel> B)) = (fb^^(length tsa)) S oo B"   
          apply (induction tsa, simp_all)
          apply (simp add: funpow_swap1)
          apply (cut_tac ts="[a]" and ts'=tsa in parallel_ID_sym)
          apply (simp add: par_assoc)
          apply (subst fb_comp_right)
          apply (simp add: fbtype_def)
          apply (subgoal_tac "fbtype (fb S) tsa ts (TI B)")
          apply simp
          apply (simp add: fbtype_def, safe)
          apply (rule TI_fb_fbtype, simp add: fbtype_def)
          by (rule TO_fb_fbtype, simp add: fbtype_def)

        lemma fb_indep_left: "\<And>S. fbtype S tsa (TO A) ts \<Longrightarrow> (fb^^(length tsa)) ((ID tsa \<parallel> A) oo S) = A oo (fb^^(length tsa)) S"   
          apply (induction tsa, simp_all)
          apply (simp add: funpow_swap1)
          apply (cut_tac ts="[a]" and ts'=tsa in parallel_ID_sym)
          apply (simp add: par_assoc)
          apply (subst fb_comp_left)
          apply (simp add: fbtype_def)
          apply (subgoal_tac "fbtype (fb S) tsa (TO A) ts")
          apply simp
          apply (simp add: fbtype_def, safe)
          apply (rule TI_fb_fbtype, simp add: fbtype_def)
          by (rule TO_fb_fbtype, simp add: fbtype_def)


       lemma TI_fb_fbtype_n: "\<And>S. fbtype S t ts ts' \<Longrightarrow> TI ((fb^^(length t)) S) = ts"
          and TO_fb_fbtype_n: "\<And>S. fbtype S t ts ts' \<Longrightarrow> TO ((fb^^(length t)) S) = ts'"
        apply (induction t)
        apply (simp add: fbtype_def)
        apply (simp add: fbtype_def)
        apply simp
        apply (simp add: funpow_swap1)
        apply (subgoal_tac "fbtype (fb S) t ts ts'")
        apply (simp add: fbtype_def)
        apply (simp add: fbtype_def)
        apply (cut_tac S=S and t=a and ts = "t@ts" and ts'="t@ts'"in  TI_fb_fbtype)
        apply (simp add: fbtype_def)
        apply (cut_tac S=S and t=a and ts = "t@ts" and ts'="t@ts'"in  TO_fb_fbtype)
        apply (simp add: fbtype_def)
        apply simp

        apply (simp add: funpow_swap1)
        apply (subgoal_tac "fbtype (fb S) t ts ts'")
        apply (simp add: fbtype_def)
        apply (simp add: fbtype_def)
        apply (cut_tac S=S and t=a and ts = "t@ts" and ts'="t@ts'"in  TI_fb_fbtype)
        apply (simp add: fbtype_def)
        apply (cut_tac S=S and t=a and ts = "t@ts" and ts'="t@ts'"in  TO_fb_fbtype)
        apply (simp add: fbtype_def)
        by simp

        declare parallel_ID [simp]
end
  
  
  locale BaseOperationFeedbacklessVars = BaseOperationFeedbackless +
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

    lemma switch_comp_subst: "set u \<subseteq> set x \<Longrightarrow> set v \<subseteq> set y \<Longrightarrow> TVs u = TVs y  \<Longrightarrow> [x \<leadsto> u] oo [y \<leadsto> v] = [x \<leadsto> Subst y u v]"
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

    lemma Switch_Split: "distinct x \<Longrightarrow>  [x \<leadsto> x @ x] = Split (TVs x)"
      by (simp add: distinct_id switch_append)

    lemma  switch_comp: "distinct x \<Longrightarrow> perm x y \<Longrightarrow> set z \<subseteq> set y \<Longrightarrow> [x\<leadsto>y] oo [y\<leadsto>z] = [x\<leadsto>z]"
        apply (subgoal_tac "distinct y")
        apply (subst switch_comp_subst, simp_all add: Subst_eq)
        using dist_perm by blast

    lemma  switch_comp_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set y \<Longrightarrow>[x\<leadsto>y] oo [y\<leadsto>z] = [x\<leadsto>z]"
      by (subst switch_comp_subst, simp_all add: Subst_eq)

      primrec newvars::"'var list \<Rightarrow> 'b list \<Rightarrow> 'var list" where
        "newvars x [] = []" |
        "newvars x (t # ts) = (let y = newvars x ts in newvar (y@x) t # y)"
        
     lemma newvars_type[simp]: "TVs(newvars x ts) = ts"
        by (induction ts, simp_all add: Let_def)

     lemma newvars_distinct[simp]: "distinct (newvars x ts)"
        apply (induction ts, simp_all add: Let_def)
        apply (subgoal_tac "newvar (newvars x ts @ x) a \<notin> set (newvars x ts @ x)")
        apply (simp del: newvar_distinct)
        by (simp only: newvar_distinct, simp) 

     lemma newvars_old_distinct[simp]: "set (newvars x ts) \<inter> set x = {}"
        apply (induction ts, simp_all add: Let_def)
        apply (subgoal_tac "newvar (newvars x ts @ x) a \<notin> set (newvars x ts @ x)")
        apply (simp del: newvar_distinct)
        by (simp only: newvar_distinct, simp)

     lemma newvars_old_distinct_a[simp]: "set x \<inter> set (newvars x ts) = {}"
        apply (cut_tac x = x and ts = ts in newvars_old_distinct)
        by (auto simp del: newvars_old_distinct)
    
     lemma newvars_length: "length(newvars x ts) = length ts"
        by (induction ts, simp_all add: Let_def)

      lemma TV_subst[simp]: "\<And> y . TVs x = TVs y \<Longrightarrow> TV (subst x y a) = TV a"
        apply (induction x, simp_all)
        apply (case_tac y, simp_all)
        by (case_tac y, auto)

      lemma TV_Subst[simp]: "TVs x = TVs y \<Longrightarrow> TVs (Subst x y z) = TVs z"
        by (induction z, simp_all)

      lemma Subst_cons: "distinct x \<Longrightarrow> a \<notin> set x \<Longrightarrow> b \<notin> set x \<Longrightarrow> length x = length y 
        \<Longrightarrow>  Subst (a # x) (b # y) z = Subst x y (Subst [a] [b] z)"
        by (induction z, simp_all)

     declare TVs_append [simp]
     declare distinct_id [simp]

      lemma par_empty_right: "A \<parallel> [[] \<leadsto> []] = A"
        by (simp)

      lemma par_empty_left: "[[] \<leadsto> []] \<parallel> A = A"
        by (simp)
      lemma  distinct_vars_comp: "distinct x \<Longrightarrow> perm x y \<Longrightarrow> [x\<leadsto>y] oo [y\<leadsto>x] = ID (TVs x)"
        by (simp add: switch_comp)
          
      lemma comp_switch_id[simp]: "distinct x \<Longrightarrow> TO S = TVs x \<Longrightarrow> S oo [x \<leadsto> x] = S"
        by (simp)

      lemma comp_id_switch[simp]: "distinct x \<Longrightarrow> TI S = TVs x \<Longrightarrow> [x \<leadsto> x] oo S = S "
        by (simp)
          
      lemma distinct_Subst_a: "\<And> v . a \<noteq> aa \<Longrightarrow> a \<notin> set v \<Longrightarrow> aa \<notin> set v \<Longrightarrow>  distinct v \<Longrightarrow> length u = length v \<Longrightarrow> subst u v a \<noteq> subst u v aa"
        apply (induction u, simp_all)
        apply (case_tac v, simp_all, auto)
        apply (metis subst_in_set subst_notin)
        by (metis subst_in_set subst_notin)

      lemma distinct_Subst_b: "\<And> v . a \<notin> set x \<Longrightarrow> distinct x \<Longrightarrow> a \<notin> set v \<Longrightarrow> distinct v \<Longrightarrow> set v \<inter> set x = {} \<Longrightarrow> length u = length v \<Longrightarrow> subst u v a \<notin> set (Subst u v x) "
        apply (induction x, simp_all)
        by (rule  distinct_Subst_a, simp_all)

      lemma distinct_Subst: "distinct u \<Longrightarrow> distinct (v @ x) \<Longrightarrow> length u = length v \<Longrightarrow> distinct (Subst u v x)"
        apply (induction x, simp_all)
        by (rule distinct_Subst_b, simp_all)

  lemma Subst_switch_more_general: "distinct u \<Longrightarrow> distinct (v @ x) \<Longrightarrow> set y \<subseteq> set x 
      \<Longrightarrow> TVs u = TVs v \<Longrightarrow> [x \<leadsto> y] = [Subst u v x \<leadsto> Subst u v y]"
        proof -
          assume [simp]: "distinct u"
          assume [simp]: "set y \<subseteq> set x"
          assume [simp]: " TVs u = TVs v"
          assume "distinct (v @ x)"
          from this have [simp]: "distinct v" and [simp]: "distinct x" and [simp]: "set v \<inter> set x = {}"
            by simp_all

          have [simp]: "length u = length v"
            by (rule TVs_length_eq, simp)

          have [simp]: "distinct (Subst u v x)"
            by (rule distinct_Subst, simp_all)

          have [simp]: "TVs (Subst u v x) = TVs x"
            by simp

          have [simp]: "Subst x (Subst u v x) y = Subst u v y"
            by (simp add: Subst_Subst)
            
          have "[x \<leadsto> y] = [Subst u v x \<leadsto> Subst u v x] oo [x \<leadsto> y]"
            by (subst comp_id_switch, simp_all)

          also have "... = [Subst u v x \<leadsto> Subst u v y]"
            by (subst switch_comp_subst, simp_all)
          finally show ?thesis
            by simp
       qed

      lemma id_par_comp: "distinct x \<Longrightarrow> TO A = TI B \<Longrightarrow> [x \<leadsto> x] \<parallel> (A oo B) = ([x \<leadsto> x] \<parallel> A ) oo ([x \<leadsto> x] \<parallel> B)"
        by (subst comp_parallel_distrib, simp_all)

      lemma par_id_comp: "distinct x \<Longrightarrow> TO A = TI B \<Longrightarrow> (A oo B) \<parallel> [x \<leadsto> x] = (A \<parallel> [x \<leadsto> x]) oo (B  \<parallel> [x \<leadsto> x])"
        by (subst comp_parallel_distrib, simp_all)

      lemma  switch_parallel_a: "distinct (x @ y) \<Longrightarrow> distinct (u @ v) \<Longrightarrow> TI S = TVs x \<Longrightarrow> TI T = TVs y \<Longrightarrow> TO S = TVs u \<Longrightarrow> TO T = TVs v \<Longrightarrow> 
        S \<parallel> T oo [u@v \<leadsto> v@u] = [x@y\<leadsto>y@x] oo T \<parallel> S"
        apply (subst switch_par)
        apply simp_all
        apply auto
        apply (simp add: comp_assoc)
        apply (subst switch_comp)
        apply simp_all
        apply auto
        apply (subst perm_tp)
        apply simp_all
        apply (subst distinct_id)
        by auto

  declare distinct_id [simp del]

  lemma fb_gen_serial: "\<And>A B v x . distinct (u @ v @ x) \<Longrightarrow> TO A = TVs (v@x) \<Longrightarrow> TI B = TVs (u @ x) \<Longrightarrow>  TVs u = TVs v 
        \<Longrightarrow> (fb ^^ length u) (([u \<leadsto> u] \<parallel> A) oo [u @ v @ x \<leadsto> v @ u @ x] oo ([v \<leadsto> v] \<parallel> B)) = A oo B"
        apply (induction u, simp)
        apply (simp add: distinct_id)
        apply (case_tac v, simp_all)
        proof safe
          fix a u A B x b v'
          assume [simp]:"TO A = TV b # TVs v' @ TVs x"
            and [simp]:"TI B = TV b # TVs v' @ TVs x"
            and [simp]:"a \<notin> set u"
            and [simp]:"TV a = TV b"
            and [simp]:"TVs u = TVs v'"
          assume [simp]: "a \<noteq> b"
          from this have [simp]: "b \<noteq> a"
            by safe
          assume [simp]:"a \<notin> set v'"
            and [simp]:"a \<notin> set x"
            and [simp]:"distinct u"
            and [simp]:"b \<notin> set v'"
            and [simp]:"distinct v'"
            and [simp]:"distinct x"
            and [simp]:"b \<notin> set x"
            and [simp]:"set v' \<inter> set x = {}"
            and [simp]:"b \<notin> set u"
          assume [simp]:"set u \<inter> set v' = {}" 
          from this have [simp]:"set v' \<inter> set u = {}"
            by blast
          assume [simp]:"set u \<inter> set x = {}"

          have [simp]: "length v' = length u"
            by (rule TVs_length_eq, simp)

          have [simp]: "perm (a # u @ b # v' @ x) (a # b # v' @ u @ x)"
            by (simp add: perm_mset )
          have [simp]: "perm (a # u @ b # v' @ x) (b # a # v' @ u @ x)"
            by (simp add: perm_mset )

          have [simp]:"perm (u @ b # v' @ x) (u @ v' @ b # x)"
            by (simp add: perm_mset )

          thm Subst_switch_more_general

          have A: "[u @ b # v' @ x \<leadsto> b # v' @ u @ x] oo [a # v' @ u @ x \<leadsto> v' @ a # u @ x] = [u @ b # v' @ x \<leadsto>  v' @ b # u @ x]"
            proof -
              have A: "[a # v' @ u @ x \<leadsto> v' @ a # u @ x] = [b # v' @ u @ x \<leadsto> v' @ b # u @ x]"
                apply (cut_tac u="[a]" and v="[b]" and x="a # v' @ u @ x" and y = "v' @ a # u @ x" in Subst_switch_more_general)
                apply simp_all
                by (simp add: Subst_append)
              have B: "[u @ b # v' @ x \<leadsto> b # v' @ u @ x] oo [a # v' @ u @ x \<leadsto> v' @ a # u @ x] = [u @ b # v' @ x \<leadsto> b # v' @ u @ x] oo [b # v' @ u @ x \<leadsto> v' @ b # u @ x]"
                by (simp add: A)
              also have "... = [u @ b # v' @ x \<leadsto>  v' @ b # u @ x]"
                apply (subst switch_comp)
                apply simp_all
                by (simp add: perm_mset union_assoc union_lcomm)
              finally show "[u @ b # v' @ x \<leadsto> b # v' @ u @ x] oo [a # v' @ u @ x \<leadsto> v' @ a # u @ x] = [u @ b # v' @ x \<leadsto>  v' @ b # u @ x]"
                by simp
              qed
          have B: "[u @ b # v' @ x \<leadsto> v' @ u @ b # x] oo [v' @ u @ a # x \<leadsto> v' @ a # u @ x] = [u @ b # v' @ x \<leadsto> v' @ b # u @ x]"
            proof -
              have A: "[v' @ u @ a # x \<leadsto> v' @ a # u @ x] = [v' @ u @ b # x \<leadsto> v' @ b # u @ x]"
                apply (cut_tac u="[a]" and v="[b]" and x="v' @ u @ a # x" and y = "v' @ a # u @ x" in Subst_switch_more_general)
                apply simp_all
                by (simp add: Subst_append)
              have B: "[u @ b # v' @ x \<leadsto> v' @ u @ b # x] oo [v' @ u @ a # x \<leadsto> v' @ a # u @ x] = [u @ b # v' @ x \<leadsto> v' @ u @ b # x] oo [v' @ u @ b # x \<leadsto> v' @ b # u @ x]"
                by (simp add: A)
              also have "... = [u @ b # v' @ x \<leadsto> v' @ b # u @ x]"
                apply (subst switch_comp)
                apply simp_all
                by (simp add: perm_mset union_assoc union_lcomm)
              finally show "[u @ b # v' @ x \<leadsto> v' @ u @ b # x] oo [v' @ u @ a # x \<leadsto> v' @ a # u @ x] = [u @ b # v' @ x \<leadsto> v' @ b # u @ x]"
                by simp
            qed
          have C: "[b # v' @ x \<leadsto> v' @ b # x] oo [u @ a # x \<leadsto> a # u @ x] = [b # v' @ x \<leadsto> b # v' @ x]"
            proof -
              have [simp]: "[u @ a # x \<leadsto> a # u @ x] = [u @ b # x \<leadsto> b # u @ x]"
                apply (cut_tac u="[a]" and v="[b]" and x="u @ a # x" and y = "a # u @ x" in Subst_switch_more_general)
                apply simp_all
                by (simp add: Subst_append)
              have [simp]: "[u @ b # x \<leadsto> b # u @ x] = [v' @ b # x \<leadsto> b # v' @ x]"
                apply (cut_tac u=u and v="v'" and x="u @ b # x" and y="b # u @ x" in Subst_switch_more_general)
                apply simp_all
                by (simp add: Subst_append)
              show  "[b # v' @ x \<leadsto> v' @ b # x] oo [u @ a # x \<leadsto> a # u @ x] = [b # v' @ x \<leadsto> b # v' @ x]"
                apply simp
                apply (subst switch_comp)
                apply simp_all
                by (simp add: perm_mset union_assoc union_lcomm)
            qed

          assume ind_hyp: "(\<And>A B v x. distinct v \<and> distinct x \<and> set v \<inter> set x = {} \<and> set u \<inter> set v = {} \<and> set u \<inter> set x = {} \<Longrightarrow>
                   TO A = TVs v @ TVs x \<Longrightarrow> TI B = TVs v @ TVs x \<Longrightarrow> TVs v' = TVs v \<Longrightarrow> (fb ^^ length u) ([u \<leadsto> u] \<parallel> A oo [u @ v @ x \<leadsto> v @ u @ x] oo [v \<leadsto> v] \<parallel> B) = A oo B)"

          define A' where "A' \<equiv> [u\<leadsto> u] \<parallel> A oo [u@b#v'@x \<leadsto> b#v'@u@x]"
          define B' where "B' \<equiv> [a#v'@u@x \<leadsto> v'@a#u@x] oo [v'\<leadsto> v'] \<parallel> B"

          define A'' where "A'' \<equiv> A oo [b#v'@x \<leadsto> v'@b#x]"
          define B'' where "B'' \<equiv> [u@a#x \<leadsto> a#u@x] oo B"

          have "fb ((fb ^^ length u) ([a # u \<leadsto> a # u] \<parallel> A oo [a # u @ b # v' @ x \<leadsto> b # v' @ a # u @ x] oo [b # v' \<leadsto> b # v'] \<parallel> B)) 
                = (fb ^^ length u) (fb ([a # u \<leadsto> a # u] \<parallel> A oo [a # u @ b # v' @ x \<leadsto> b # v' @ a # u @ x] oo [b # v' \<leadsto> b # v'] \<parallel> B))"
            by (simp add: funpow_swap1)
          also have "... = (fb ^^ length u) (fb (([[a] \<leadsto> [a]] \<parallel> A') oo [a # b # v'@ u @ x \<leadsto> b # a # v'@ u @ x] oo ([[b] \<leadsto> [b]] \<parallel> B')))"
            proof (simp add: A'_def B'_def)
              have "[[a] \<leadsto> [a]] \<parallel> ([u \<leadsto> u] \<parallel> A oo [u @ b # v' @ x \<leadsto> b # v' @ u @ x]) oo 
                        [a # b # v' @ u @ x \<leadsto> b # a # v' @ u @ x] oo [[b] \<leadsto> [b]] \<parallel> ([a # v' @ u @ x \<leadsto> v' @ a # u @ x] oo [v' \<leadsto> v'] \<parallel> B) = 
                    ([a#u \<leadsto> a#u] \<parallel> A oo [a#u @ b # v' @ x \<leadsto> a#b # v' @ u @ x]) oo 
                        [a # b # v' @ u @ x \<leadsto> b # a # v' @ u @ x] oo ([b#a # v' @ u @ x \<leadsto> b#v' @ a # u @ x] oo [b#v' \<leadsto> b#v'] \<parallel> B)"
                apply (subst id_par_comp, simp_all)
                apply (subst id_par_comp, simp_all)
                apply (simp add: par_assoc [THEN sym] par_switch)
                by (subst par_switch, simp_all, auto)
              also have "... = [a#u \<leadsto> a#u] \<parallel> A oo ([a#u @ b # v' @ x \<leadsto> a#b # v' @ u @ x] oo 
                        [a # b # v' @ u @ x \<leadsto> b # a # v' @ u @ x] oo [b#a # v' @ u @ x \<leadsto> b#v' @ a # u @ x]) oo [b#v' \<leadsto> b#v'] \<parallel> B"
                by (simp add: comp_assoc)
              also have "... = [a#u \<leadsto> a#u] \<parallel> A oo ([a#u @ b # v' @ x \<leadsto> b#v' @ a # u @ x]) oo [b#v' \<leadsto> b#v'] \<parallel> B"
                apply (subst switch_comp, simp_all)
                 using \<open>a # u @ b # v' @ x <~~> a # b # v' @ u @ x\<close> apply auto[1]
                apply auto [1]
                by (subst switch_comp, simp_all)
            finally show "(fb ^^ length u) (fb ([a # u \<leadsto> a # u] \<parallel> A oo [a # u @ b # v' @ x \<leadsto> b # v' @ a # u @ x] oo [b # v' \<leadsto> b # v'] \<parallel> B)) =
              (fb ^^ length u)
               (fb ([[a] \<leadsto> [a]] \<parallel> ([u \<leadsto> u] \<parallel> A oo [u @ b # v' @ x \<leadsto> b # v' @ u @ x]) oo [a # b # v' @ u @ x \<leadsto> b # a # v' @ u @ x] oo [[b] \<leadsto> [b]] \<parallel> ([a # v' @ u @ x \<leadsto> v' @ a # u @ x] oo [v' \<leadsto> v'] \<parallel> B)))"
               by simp

            qed
          also have "... = (fb ^^ length u) (A' oo B')"
            by (subst fb_serial, simp_all add: A'_def B'_def)
          also have "... = (fb ^^ length u) ([u \<leadsto> u] \<parallel> A'' oo [u@v'@b#x \<leadsto> v'@u@b#x] oo [v' \<leadsto> v'] \<parallel> B'')"
            apply (simp add: A'_def B'_def A''_def B''_def)
            apply (subst id_par_comp, simp_all)
            apply (subst id_par_comp, simp_all)
            apply (simp add: par_switch)
            apply (rule_tac f = "fb ^^ length u" in arg_cong)
            apply (simp add: comp_assoc [THEN sym])
            apply (rule_tac f = "\<lambda> X . X oo [v' \<leadsto> v'] \<parallel> B" in arg_cong)
            apply (simp add: comp_assoc)
            apply (rule_tac f = "\<lambda> X . [u \<leadsto> u] \<parallel> A oo X" in arg_cong)
            apply (simp add: comp_assoc [THEN sym])
            apply (subst switch_comp)
               apply auto [3]
              apply (simp add: perm_append_Cons)
            by (simp add: A  B)
          also have "... = A'' oo B''"
            apply (rule ind_hyp, simp_all)
            apply (simp add: A''_def)
            by (simp add: B''_def)
          also have "... = A oo ([b # v' @ x \<leadsto> v' @ b # x] oo [u @ a # x \<leadsto> a # u @ x]) oo B"
            apply (simp add: A''_def B''_def)
            by (simp add: comp_assoc)
          also have "... = A oo B"
            by (simp add: C)

          finally show "fb ((fb ^^ length u) ([a # u \<leadsto> a # u] \<parallel> A oo [a # u @ b # v' @ x \<leadsto> b # v' @ a # u @ x] oo [b # v' \<leadsto> b # v'] \<parallel> B)) = A oo B"
            by simp
        qed


      lemma fb_par_serial: "distinct(u @ x @ x') \<Longrightarrow> distinct (u @ y @ x') \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs (u@y) \<Longrightarrow> TI B = TVs (u@x') \<Longrightarrow> TO B = TVs y' \<Longrightarrow>
        (fb^^(length u)) ([u @ x @ x' \<leadsto> x @ u @ x'] oo (A \<parallel> B)) = (A \<parallel> ID (TVs x') oo [u @ y @ x' \<leadsto> y @ u @ x'] oo ID (TVs y) \<parallel> B)"
        proof -
          assume A: "distinct (u @ y @ x')"
          assume E: "distinct(u @ x @ x')"
          assume [simp]: "TO A = TVs (u@y)"
          assume [simp]: "TI A = TVs x"
          assume [simp]: "TI B = TVs (u@x')"
          define v where "v \<equiv> newvars (u @ x @ x' @ y) (TVs u)"
          have B: "distinct (u @ v @ y @ x')"
            apply (cut_tac x = "u @ x @ x' @ y" and ts = "TVs u" in newvars_old_distinct)
            apply (unfold v_def [THEN symmetric])
            apply (cut_tac A, simp_all)
            apply safe
             apply (simp add: v_def)
             by blast

          have F: "distinct ((v @ y @ u) @ x')"
            apply (cut_tac x = "u @ x @ x' @ y" and ts = "TVs u" in newvars_old_distinct)
            apply (unfold v_def [THEN symmetric])
            apply (cut_tac A, simp_all)
            apply (simp add: v_def)
              by blast

          have [simp]: "TVs v= TVs u"
            by (simp add: v_def)
          have AA: "(fb ^^ length u) ([u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) oo [u @ v @ y @ x' \<leadsto> v @ u @ y @ x'] oo [v \<leadsto> v] \<parallel> ([u @ y @ x' \<leadsto> y @ u @ x'] oo [y \<leadsto> y] \<parallel> B)) 
              = A \<parallel> [x' \<leadsto> x'] oo ([u @ y @ x' \<leadsto> y @ u @ x'] oo [y \<leadsto> y] \<parallel> B)"
            apply (cut_tac x = "y @ x'" and u = u and v = v  and A = "A \<parallel> [x' \<leadsto> x']" and B = "[u @ y @ x' \<leadsto> y @ u @ x'] oo ([y \<leadsto> y] \<parallel> B)" in fb_gen_serial)
            by (cut_tac B, simp, simp_all)

          (*use "[v \<leadsto> v] \<parallel> (A oo B) = [v \<leadsto> v] \<parallel> A oo [v \<leadsto> v] \<parallel> B"*)  
          have C: "[v \<leadsto> v] \<parallel> ([u @ y @ x' \<leadsto> y @ u @ x'] oo [y \<leadsto> y] \<parallel> B) = [v @ u @ y @ x' \<leadsto> v @ y @ u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B"
            apply (subst id_par_comp, simp_all)
            apply (simp add: v_def)
            apply (subst par_assoc [THEN sym])
            apply (subst par_switch)
            apply (cut_tac F, auto)
            apply (subst par_switch)
            by (cut_tac F, auto)

          have "[u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) oo [u @ v @ y @ x' \<leadsto> v @ u @ y @ x'] oo [v \<leadsto> v] \<parallel> ([u @ y @ x' \<leadsto> y @ u @ x'] oo [y \<leadsto> y] \<parallel> B) = 
           [u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) oo [u @ v @ y @ x' \<leadsto> v @ u @ y @ x'] oo ([v @ u @ y @ x' \<leadsto> v @ y @ u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B)"
           by (simp add: C)
          also have "... = [u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) oo ([u @ v @ y @ x' \<leadsto> v @ u @ y @ x'] oo [v @ u @ y @ x' \<leadsto> v @ y @ u @ x']) oo [v @ y \<leadsto> v @ y] \<parallel> B"
            by (simp add: comp_assoc)
          also have "... = [u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) oo [u @ v @ y @ x' \<leadsto> v @ y @ u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B"
            apply (subst switch_comp, simp_all)
            apply (cut_tac B, simp)
            apply (simp add: perm_mset)
            by auto

          thm switch_par

         also have "... = ([u @ x @ x' \<leadsto> x @ u @ x'] oo (A \<parallel> [u @ x' \<leadsto> u @ x']) oo [v @ y @ u @ x' \<leadsto> u @ v @ y @ x']) oo  [u @ v @ y @ x' \<leadsto> v @ y @ u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B"
          apply (subgoal_tac "[u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) = [u @ x @ x' \<leadsto> x @ u @ x'] oo A \<parallel> [u @ x' \<leadsto> u @ x'] oo [v @ y @ u @ x' \<leadsto> u @ v @ y @ x']", simp_all)
          apply (subst par_assoc [THEN sym])
          apply (subst switch_par [of "u" "x" "v @ y" "u"])
          apply (cut_tac E, simp)
                apply (cut_tac B)
                apply simp
             apply blast
          apply simp_all
          apply (subst par_id_comp)
          apply (cut_tac A, simp)
          apply (subst TO_comp, simp_all)
          apply (subst par_id_comp)
          apply (cut_tac A, simp)
          apply (subst TI_par, simp_all)
          apply (subst par_assoc)
          apply (subst par_switch)
          apply (cut_tac E, simp_all)
          apply (subst par_switch)
          apply (cut_tac E, simp_all)
          apply (subst par_switch)
          by (cut_tac F, simp_all, auto)

         also have "... = [u @ x @ x' \<leadsto> x @ u @ x'] oo (A \<parallel> [u @ x' \<leadsto> u @ x']) oo ([v @ y @ u @ x' \<leadsto> u @ v @ y @ x'] oo  [u @ v @ y @ x' \<leadsto> v @ y @ u @ x']) oo [v @ y \<leadsto> v @ y] \<parallel> B"
          by (simp add: comp_assoc)


         also have "... = [u @ x @ x' \<leadsto> x @ u @ x'] oo (A \<parallel> [u @ x' \<leadsto> u @ x']) oo [v @ y \<leadsto> v @ y] \<parallel> B"
          apply (subst switch_comp)
          apply (cut_tac F, simp)
          apply (simp add: add.left_commute perm_mset)
          using F TO_comp by auto
         also have "... = [u @ x @ x' \<leadsto> x @ u @ x'] oo (A \<parallel> [u @ x' \<leadsto> u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B)"
          using local.comp_assoc by auto
         also have "... =([u @ x @ x' \<leadsto> x @ u @ x'] oo A \<parallel> B)"
          apply (subgoal_tac "(A \<parallel> [u @ x' \<leadsto> u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B) = A \<parallel> B")
          apply (simp_all)
          apply (subst comp_parallel_distrib, simp_all)
          apply (subst comp_switch_id, simp_all)
          apply (cut_tac B, simp)
          apply (subst comp_id_switch, simp_all)
          by (cut_tac B, simp)

         finally have [simp]: "[u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) oo [u @ v @ y @ x' \<leadsto> v @ u @ y @ x'] oo [v \<leadsto> v] \<parallel> ([u @ y @ x' \<leadsto> y @ u @ x'] oo [y \<leadsto> y] \<parallel> B) = 
           ([u @ x @ x' \<leadsto> x @ u @ x'] oo A \<parallel> B)"
           by simp

        show ?thesis
          apply (cut_tac AA)
          apply simp
          using F distinct_id local.comp_assoc by auto
      qed


      (*!!!*)
      (*to prove this using dist x, s, t and set u \<subseteq> set x and set v \<subseteq> set x \<Longrightarrow> x[x \<rightarrow> u @ v] oo ([u \<rightarrow> s] ||| [v \<rightarrow> t]) = [x \<rightarrow> s @ t]*)
      (* TO CHECK \<rightarrow> the axiom still requires set (In A) \<inter> set (In B) = {}, etc.) \<rightarrow> maybe needs to be changed *)


      lemma switch_newvars: "distinct x \<Longrightarrow> [newvars w (TVs x) \<leadsto> newvars w (TVs x)] = [x \<leadsto> x]"
        by (simp add: distinct_id)


      lemma switch_par_comp_Subst: "distinct x \<Longrightarrow> distinct y' \<Longrightarrow> distinct z' \<Longrightarrow> set y \<subseteq> set x 
      \<Longrightarrow> set z \<subseteq> set x 
        \<Longrightarrow> set u \<subseteq> set y' \<Longrightarrow> set v \<subseteq> set z' \<Longrightarrow> TVs y = TVs y' \<Longrightarrow> TVs z = TVs z' \<Longrightarrow>
        [x \<leadsto> y @ z] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> v] = [x \<leadsto> Subst y' y u @ Subst z' z v]"
        proof -
          assume [simp]: "distinct y'"
          assume [simp]: "set u \<subseteq> set y'"
          assume [simp]: "distinct z'"
          assume [simp]: "set v \<subseteq> set z'"
          assume [simp]: "distinct x"
          assume [simp]: "TVs y = TVs y'"
          assume [simp]: "TVs z = TVs z'"
          assume "set y \<subseteq> set x"
          assume "set z \<subseteq> set x"

          define y'' where "y'' \<equiv> newvars (y' @ z') (TVs y')"

          have [simp]: "distinct y''"
            by (simp add: y''_def)

          have [simp]: "set y' \<inter> set y'' = {}"
            by (metis Un_iff disjoint_iff_not_equal newvars_old_distinct_a set_append y''_def)

          have [simp]: "set y'' \<inter> set z' = {}"
            by (metis Un_iff disjoint_iff_not_equal newvars_old_distinct_a set_append y''_def)

          have [simp]: "TVs y' = TVs y''"
            by (simp add: y''_def)            

          have [simp]: "length y' = length y''"
            by (rule TVs_length_eq, simp)

          have [simp]: "TVs y = TVs y''"
            by simp

          have [simp]: "length y'' = length y"
            by (metis  \<open>TVs y = TVs y''\<close> TVs_length_eq)

          have [simp]: "length z' = length z"
            by (metis \<open>TVs z = TVs z'\<close> TVs_length_eq)

          have [simp]: "set z' \<inter> set (Subst y' y'' u) = {}"
            apply (subgoal_tac "set (Subst y' y'' u) \<subseteq> set y''")
            apply (subgoal_tac "set z' \<inter> set y'' = {}")
            apply blast
            apply (simp add: Int_commute)
            by (subst Subst_set_incl, simp_all)

          have [simp]: "Subst y'' y (Subst y' y'' u) = (Subst y' y u)"
            by (rule Subst_Subst_a, simp_all)

          have [simp]: "Subst (y'' @ z') (y @ z) (Subst y' y'' u) = (Subst y' y u)"
            apply (subst Subst_not_in)
            by simp_all

          have [simp]: "set y'' \<inter> set v = {}"
            apply (subgoal_tac "set v \<subseteq> set z'")
            apply (subgoal_tac "set y'' \<inter> set z' = {}")
            apply blast
            by simp_all

          have [simp]: "Subst (y'' @ z') (y @ z) v = (Subst z' z v)"
            by (subst Subst_not_in_a, simp_all)

          have [simp]: "Subst (y'' @ z') (y @ z) ((Subst y' y'' u) @ v) = ((Subst y' y u) @ (Subst z' z v))"
            by (simp add: Subst_append)

          have "[x \<leadsto> y @ z] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> v] = [x \<leadsto> y @ z] oo [y'' \<leadsto> Subst y' y'' u] \<parallel> [z' \<leadsto> v]"
            by (cut_tac x=y' and y=u and u = y' and v =y'' in Subst_switch_more_general, simp_all add: Int_commute)
          also have "... = [x \<leadsto> y @ z] oo [y'' @ z' \<leadsto> (Subst y' y'' u) @ v]"
            apply (subst par_switch, simp_all)
            by (subst Subst_set_incl, simp_all)
          also have "... = [x \<leadsto> Subst (y'' @ z') (y @ z) ((Subst y' y'' u) @ v)]"
            apply (subst switch_comp_subst, auto)
            using \<open>set y \<subseteq> set x\<close> apply auto [1]
            using \<open>set z \<subseteq> set x \<close> apply auto [1]
            using Subst_set_incl \<open>length y' = length y''\<close> \<open>set u \<subseteq> set y'\<close> apply blast
            using \<open>set v \<subseteq> set z'\<close> by blast
          also have "... = [x \<leadsto> (Subst y' y u) @ (Subst z' z v)]"
            by simp
          finally show ?thesis
            by simp
        qed
            
      lemma switch_par_comp: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> distinct z \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x 
        \<Longrightarrow> set y' \<subseteq> set y \<Longrightarrow> set z' \<subseteq> set z \<Longrightarrow> [x \<leadsto> y @ z] oo [y \<leadsto> y'] \<parallel> [z \<leadsto> z'] = [x \<leadsto> y' @ z']"
        by (subst switch_par_comp_Subst, simp_all add: Subst_eq)

      lemma par_switch_eq: "distinct u \<Longrightarrow> distinct v \<Longrightarrow> distinct y' \<Longrightarrow> distinct z' 
            \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs v \<Longrightarrow> TI C = TVs v @ TVs y \<Longrightarrow> TVs y = TVs y' \<Longrightarrow>
            TI C' = TVs v @ TVs z \<Longrightarrow> TVs z = TVs z' \<Longrightarrow>
            set x \<subseteq> set u \<Longrightarrow> set y \<subseteq> set u \<Longrightarrow> set z \<subseteq> set u \<Longrightarrow> 
            [v \<leadsto> v] \<parallel> [u \<leadsto> y] oo C = [v \<leadsto> v] \<parallel> [u \<leadsto> z] oo C' 
            \<Longrightarrow> [u \<leadsto> x @ y] oo ( A \<parallel> [y' \<leadsto> y']) oo C = [u \<leadsto> x @ z] oo ( A \<parallel> [z' \<leadsto> z']) oo C'"
        proof -
          assume [simp]: "distinct u"
          assume [simp]: "set x \<subseteq> set u"
          assume [simp]: "set y \<subseteq> set u"
          assume [simp]: "TVs y = TVs y'"
          assume [simp]: "TI A = TVs x"
          assume [simp]: "distinct y'"
          assume [simp]: "TO A = TVs v"
          assume [simp]: "distinct v"
          assume [simp]: "TI C = TVs v @ TVs y"
          assume eq: "[v \<leadsto> v] \<parallel> [u \<leadsto> y] oo C = [v \<leadsto> v] \<parallel> [u \<leadsto> z] oo C'"
          assume [simp]: "TI C' = TVs v @ TVs z"
          assume [simp]: "TVs z = TVs z'"
          assume [simp]: "distinct z'"
          assume [simp]: "set z \<subseteq> set u"

          define x' where "x' \<equiv> newvars (x @ u) (TVs x)"

          have [simp]: "distinct x'"
            by (simp add: x'_def)

          have [simp]: "TVs x' = TVs x"
            by (simp add: x'_def)

          have [simp]: "length x' = length x"
            by (metis \<open>TVs x' = TVs x\<close> TVs_length_eq)

          have "[u \<leadsto> x @ y] oo ( A \<parallel> [y' \<leadsto> y']) oo C = ([u \<leadsto> x @ u] oo [x' \<leadsto> x'] \<parallel> [u \<leadsto> y]) oo ( A \<parallel> [y' \<leadsto> y']) oo C"
            by (simp add: switch_par_comp_Subst Subst_eq)
          also have "... = [u \<leadsto> x @ u] oo ([x' \<leadsto> x'] \<parallel> [u \<leadsto> y] oo  A \<parallel> [y' \<leadsto> y']) oo C"
            by (simp add: comp_assoc)
          also have "... = [u \<leadsto> x @ u] oo A \<parallel> [u \<leadsto> y] oo C"
            by (simp add: comp_parallel_distrib  )
          also have "... = [u \<leadsto> x @ u] oo (A \<parallel> [u \<leadsto> u] oo [v \<leadsto> v] \<parallel> [u \<leadsto> y]) oo C"
            by (simp add: comp_parallel_distrib)
          also have "... = [u \<leadsto> x @ u] oo A \<parallel> [u \<leadsto> u] oo ([v \<leadsto> v] \<parallel> [u \<leadsto> y] oo C)"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> x @ u] oo A \<parallel> [u \<leadsto> u] oo ([v \<leadsto> v] \<parallel> [u \<leadsto> z] oo C')"
            by (simp add: eq)
          also have "... = [u \<leadsto> x @ u] oo (A \<parallel> [u \<leadsto> u] oo [v \<leadsto> v] \<parallel> [u \<leadsto> z]) oo C'"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> x @ u] oo A \<parallel> [u \<leadsto> z] oo C'"
            by (simp add: comp_parallel_distrib)
          also have "... = [u \<leadsto> x @ u] oo ([x' \<leadsto> x'] \<parallel> [u \<leadsto> z] oo A \<parallel> [z' \<leadsto> z']) oo C'"
            by (simp add: comp_parallel_distrib)
          also have "... = ([u \<leadsto> x @ u] oo [x' \<leadsto> x'] \<parallel> [u \<leadsto> z]) oo A \<parallel> [z' \<leadsto> z'] oo C'"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> x @ z] oo A \<parallel> [z' \<leadsto> z'] oo C'"
            by (simp add: switch_par_comp_Subst Subst_eq)
          finally show ?thesis
            by simp
        qed

      lemma paralle_switch: "\<exists> x y u v. distinct (x @ y) \<and> distinct (u @ v) \<and> TVs x = TI A 
        \<and> TVs u = TO A \<and> TVs y = TI B \<and> 
        TVs v = TO B \<and> A \<parallel> B = [x @ y \<leadsto> y @ x] oo (B \<parallel> A) oo [v @ u \<leadsto> u @ v]"
        apply (rule_tac x="newvars [] (TI A)" in exI)
        apply (rule_tac x="newvars (newvars [] (TI A)) (TI B)" in exI)
        apply (rule_tac x="newvars [] (TO A)" in exI)
        apply (rule_tac x="newvars (newvars [] (TO A)) (TO B)" in exI)
        by (subst switch_par, simp_all)

      lemma par_switch_eq_dist: "distinct (u @ v) \<Longrightarrow> distinct y' \<Longrightarrow> distinct z' \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs v \<Longrightarrow> TI C = TVs v @ TVs y \<Longrightarrow> TVs y = TVs y' \<Longrightarrow>
            TI C' = TVs v @ TVs z \<Longrightarrow> TVs z = TVs z' \<Longrightarrow>
            set x \<subseteq> set u \<Longrightarrow> set y \<subseteq> set u \<Longrightarrow> set z \<subseteq> set u \<Longrightarrow> 
            [v @ u \<leadsto> v @ y] oo C = [v @ u \<leadsto> v @ z] oo C' \<Longrightarrow> [u \<leadsto> x @ y] oo ( A \<parallel> [y' \<leadsto> y']) oo C = [u \<leadsto> x @ z] oo ( A \<parallel> [z' \<leadsto> z']) oo C'"  
        apply (rule  par_switch_eq, simp_all)
        by (simp add: par_switch Int_commute)

      lemma par_switch_eq_dist_a: "distinct (u @ v) \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs v \<Longrightarrow> TI C = TVs v @ TVs y \<Longrightarrow> TVs y = ty \<Longrightarrow> TVs z = tz \<Longrightarrow>
            TI C' = TVs v @ TVs z \<Longrightarrow> set x \<subseteq> set u \<Longrightarrow> set y \<subseteq> set u \<Longrightarrow> set z \<subseteq> set u \<Longrightarrow> 
            [v @ u \<leadsto> v @ y] oo C = [v @ u \<leadsto> v @ z] oo C' \<Longrightarrow> [u \<leadsto> x @ y] oo A \<parallel> ID ty oo C = [u \<leadsto> x @ z] oo A \<parallel> ID tz oo C'"
        apply (cut_tac y' = "newvars [] ty" and z' = "newvars [] tz" and C = C 
            and x = x and y = y and z = z in par_switch_eq_dist, simp_all)
        by (simp add: distinct_id)


      lemma par_switch_eq_a: "distinct (u @ v) \<Longrightarrow> distinct y' \<Longrightarrow> distinct z' \<Longrightarrow> distinct t' \<Longrightarrow> distinct s'
            \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs v \<Longrightarrow> TI C = TVs t @ TVs v @ TVs y \<Longrightarrow> TVs y = TVs y' \<Longrightarrow>
            TI C' = TVs s @  TVs v @ TVs z \<Longrightarrow> TVs z = TVs z' \<Longrightarrow> TVs t = TVs t' \<Longrightarrow>  TVs s = TVs s' \<Longrightarrow>
            set t \<subseteq> set u \<Longrightarrow> set x \<subseteq> set u \<Longrightarrow> set y \<subseteq> set u \<Longrightarrow> set s \<subseteq> set u \<Longrightarrow> set z \<subseteq> set u \<Longrightarrow>
            [u @ v \<leadsto> t @ v @ y] oo C = [u @ v \<leadsto> s @ v @ z] oo C' \<Longrightarrow> 
            [u \<leadsto> t @ x @ y] oo ([t' \<leadsto> t'] \<parallel> A \<parallel> [y' \<leadsto> y']) oo C = [u \<leadsto> s @ x @ z] oo ([s' \<leadsto> s'] \<parallel> A \<parallel> [z' \<leadsto> z']) oo C'"
        proof -

          assume [simp]: "distinct (u @ v)"
          assume [simp]: "distinct y'"
          assume [simp]: "distinct z'"
          assume [simp]: "distinct t'"
          assume [simp]: "distinct s'"
          assume [simp]: "set t \<subseteq> set u"
          assume [simp]: "set x \<subseteq> set u"
          assume [simp]: "set y \<subseteq> set u"
          assume [simp]: "set s \<subseteq> set u"
          assume [simp]: "set z \<subseteq> set u"
          assume [simp]: "TVs y = TVs y'"
          assume [simp]: "TVs t = TVs t'"
          assume [simp]: "TVs s = TVs s'"
          assume [simp]: "TVs z = TVs z'"
          assume [simp]: "TI A = TVs x"
          assume [simp]: "TO A = TVs v"
          assume [simp]: "TI C = TVs t @ TVs v @ TVs y"
          assume [simp]: "TI C' = TVs s @  TVs v @ TVs z"
          assume eq: "[u @ v \<leadsto> t @ v @ y] oo C = [u @ v \<leadsto> s @ v @ z] oo C'"

          define x' where "x' \<equiv> newvars u (TVs x)"
          define y'' where "y'' \<equiv> newvars (x' @ v) (TVs y')"
          define z'' where "z'' \<equiv> newvars (x' @ v) (TVs z')"


          have [simp]: "distinct u"
            using \<open>distinct (u @ v)\<close> by fastforce

          have [simp]: "distinct v"
            using \<open>distinct (u @ v)\<close> by fastforce

          have [simp]: "set u \<inter> set v = {}"
            using \<open>distinct (u @ v)\<close> by fastforce


          have [simp]: "distinct x'"
            by (simp add: x'_def)

          have [simp]: "set u \<inter> set x' = {}"
            by (simp add: x'_def)

          have [simp]: "TVs x' = TVs x"
            by (simp add: x'_def)

          have [simp]: "length x' = length x"
            by (metis \<open>TVs x' = TVs x\<close> TVs_length_eq)

          have [simp]: "set x' \<inter> set t = {}"
            using \<open>set t \<subseteq> set u\<close> \<open>set u \<inter> set x' = {}\<close> by blast

          have [simp]: "set x' \<inter> set y = {}"
            using \<open>set y \<subseteq> set u\<close> \<open>set u \<inter> set x' = {}\<close> by blast

          have [simp]: "distinct y''"
            by (simp add: y''_def)

          have [simp]: "set x' \<inter> set y'' = {}"
            by (metis Diff_disjoint Int_commute diff_disjoint diff_union inter_subset newvars_old_distinct_a set_diff set_inter y''_def)

          have [simp]: "set y'' \<inter> set v = {}"
            by (metis Diff_disjoint Int_commute diff_disjoint diff_union newvars_old_distinct_a set_diff set_inter y''_def)

          have [simp]: "TVs y'' = TVs y'"
            by (simp add: y''_def)

          have [simp]: "length t' = length t"
            by (metis \<open>TVs t = TVs t'\<close> TVs_length_eq)

          have [simp]: "length y' = length y"
            by (metis \<open>TVs y = TVs y'\<close> TVs_length_eq)

          have B: "TVs y'' = TVs y" 
            by (simp add: y''_def)

          have [simp]: "length y'' = length y"
            by (metis \<open>TVs y'' = TVs y\<close> TVs_length_eq)

          have [simp]: "set t \<subseteq> set u \<union> set x'"
            by (metis Un_subset_iff \<open>set t \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "set y \<subseteq> set u \<union> set x'"
            by (metis Un_subset_iff \<open>set y \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "set t \<subseteq> set u \<union> set v"
            by (metis Un_subset_iff \<open>set t \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "set y \<subseteq> set u \<union> set v"
            by (metis Un_subset_iff \<open>set y \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "distinct z''"
            by (simp add: z''_def)

          have [simp]: "set z'' \<inter> set v = {}"
            by (metis Diff_disjoint diff_disjoint diff_union newvars_old_distinct_a set_diff z''_def)
            
          have [simp]: "set s \<subseteq> set u \<union> set v"
            by (metis Un_subset_iff \<open>set s \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "set z \<subseteq> set u \<union> set v"
            by (metis Un_subset_iff \<open>set z \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "TVs z' = TVs z''"
            by (simp add: z''_def)

          have [simp]: "length s' = length s"
            by (metis  \<open>TVs s = TVs s'\<close> TVs_length_eq)

          have [simp]: "length z' = length z"
            by (metis  \<open>TVs z = TVs z'\<close> TVs_length_eq)

          have A: "TVs z'' = TVs z"
            by simp

          have [simp]: "length z'' = length z"
            by (metis \<open>TVs z'' = TVs z\<close> TVs_length_eq)

          have [simp]: "set x' \<inter> set z'' = {}"
            by (metis Int_commute inf_bot_right inf_left_commute inf_sup_absorb newvars_old_distinct_a set_append z''_def)

          have [simp]: "set s \<subseteq> set u \<union> set x'"
            by (metis Un_subset_iff \<open>set s \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "set z \<subseteq> set u \<union> set x'"
            by (metis Un_subset_iff \<open>set z \<subseteq> set u\<close> sup.absorb_iff1 sup_ge1)

          have [simp]: "set x' \<inter> set s = {}"
            using \<open>set s \<subseteq> set u\<close> \<open>set u \<inter> set x' = {}\<close> by blast

          have [simp]: "set x' \<inter> set z = {}"
            using \<open>set z \<subseteq> set u\<close> \<open>set u \<inter> set x' = {}\<close> by blast

          have "[u \<leadsto> t @ x @ y] oo ([t' \<leadsto> t'] \<parallel> A \<parallel> [y' \<leadsto> y']) oo C = ([u \<leadsto> u @ x] oo [u @ x' \<leadsto> t @ x' @ y]) oo ([t' \<leadsto> t'] \<parallel> A \<parallel> [y' \<leadsto> y']) oo C"
            apply (subst switch_comp_subst, simp_all)
            by (simp add: Subst_append Subst_not_in Subst_not_in_a Subst_eq)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> t @ x' @ y] oo [t' \<leadsto> t'] \<parallel> A \<parallel> [y' \<leadsto> y']) oo C"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> t @ x' @ y] oo [t' \<leadsto> t'] \<parallel> (A \<parallel> [y' \<leadsto> y'])) oo C"
            by (simp add: par_assoc)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> t @ x' @ y] oo [t' \<leadsto> t'] \<parallel> (A \<parallel> [y'' \<leadsto> y''])) oo C"
            by (simp add: y''_def switch_newvars)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> t @ x' @ y] oo [t' \<leadsto> t'] \<parallel> ([x' @ y'' \<leadsto> y'' @ x'] oo [y'' \<leadsto> y''] \<parallel> A oo [y'' @ v \<leadsto> v @ y''])) oo C"
            by (subst(2) switch_par, simp_all)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> t @ x' @ y] oo ([t' \<leadsto> t'] \<parallel> [x' @ y'' \<leadsto> y'' @ x'] oo [t' \<leadsto> t'] \<parallel> ([y'' \<leadsto> y''] \<parallel> A) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''])) oo C"
            by (simp add: comp_parallel_distrib  )
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> t @ x' @ y] oo [t' \<leadsto> t'] \<parallel> [x' @ y'' \<leadsto> y'' @ x']) oo [t' \<leadsto> t'] \<parallel> ([y'' \<leadsto> y''] \<parallel> A) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> u @ x] oo [u @ x' \<leadsto> (Subst t' t t') @ (Subst (x' @ y'') (x' @ y) (y'' @ x'))] oo [t' \<leadsto> t'] \<parallel> ([y'' \<leadsto> y''] \<parallel> A) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: switch_par_comp_Subst)
          also have "... = [u \<leadsto> u @ x] oo [u @ x' \<leadsto> t @ y @ x'] oo [t' \<leadsto> t'] \<parallel> ([y'' \<leadsto> y''] \<parallel> A) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: Subst_append Subst_not_in Subst_not_in_a Subst_eq Int_commute)
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> t @ y] \<parallel> [x' \<leadsto> x'] oo ([t' \<leadsto> t'] \<parallel> [y'' \<leadsto> y'']) \<parallel> A oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            apply (simp add: par_assoc)
            by (cut_tac x="u" and x'="t@y" and y="x'" and y'="x'" in par_switch, simp_all)
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> t @ y] \<parallel> [x' \<leadsto> x'] oo ([t' \<leadsto> t'] \<parallel> [y'' \<leadsto> y'']) \<parallel> A) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: comp_assoc )
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> t @ y] oo ([t' \<leadsto> t'] \<parallel> [y'' \<leadsto> y''])) \<parallel> A oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: comp_parallel_distrib)
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> t @ y] \<parallel> A oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: switch_par_comp_Subst)
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> u] oo [u \<leadsto> t @ y]) \<parallel> (A oo [v \<leadsto> v]) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: )
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> u] \<parallel> A  oo [u \<leadsto> t @ y] \<parallel> [v \<leadsto> v]) oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y''] oo C"
            by (simp add: comp_parallel_distrib )
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> u] \<parallel> A  oo ([u @ v \<leadsto> t @ y @ v] oo [t' \<leadsto> t'] \<parallel> [y'' @ v \<leadsto> v @ y'']) oo C"
            by (simp add: comp_assoc par_switch  )
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> u] \<parallel> A  oo [u @ v \<leadsto> t @ v @ y] oo C"
            apply (simp add: switch_par_comp_Subst Subst_append Subst_not_in_a)
            apply (subst Subst_not_in, simp_all)
            using \<open>set y'' \<inter> set v = {}\<close> by blast
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> u] \<parallel> A  oo ([u @ v \<leadsto> t @ v @ y] oo C)"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> u] \<parallel> A oo ([u @ v \<leadsto> s @ v @ z] oo C')"
            by (simp add: eq)
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> u] \<parallel> A oo [u @ v \<leadsto> s @ v @ z] oo C'"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> u] \<parallel> A  oo ([u @ v \<leadsto> s @ z @ v] oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z'']) oo C'"
            apply (subst switch_par_comp_Subst, simp_all)
            apply (simp add: Subst_append Subst_not_in_a)
            apply (subst Subst_not_in, simp_all)
            using \<open>set z'' \<inter> set v = {}\<close> by blast
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> u] \<parallel> A  oo [u \<leadsto> s @ z] \<parallel> [v \<leadsto> v]) oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            apply (simp add: comp_assoc  )
            by (cut_tac x=u and x'="s@z" and y=v and y'=v in par_switch, simp_all)
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> s @ z] \<parallel> A oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            by (simp add: comp_parallel_distrib)
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> s @ z] oo ([s' \<leadsto> s'] \<parallel> [z'' \<leadsto> z''])) \<parallel> A oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            by (simp add: switch_par_comp_Subst)
          also have "... = [u \<leadsto> u @ x] oo ([u \<leadsto> s @ z] \<parallel> [x' \<leadsto> x'] oo ([s' \<leadsto> s'] \<parallel> [z'' \<leadsto> z'']) \<parallel> A) oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            by (subst comp_parallel_distrib, simp_all)
          also have "... = [u \<leadsto> u @ x] oo [u \<leadsto> s @ z] \<parallel> [x' \<leadsto> x'] oo ([s' \<leadsto> s'] \<parallel> [z'' \<leadsto> z'']) \<parallel> A oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> u @ x] oo [u @ x' \<leadsto> s @ z @ x'] oo [s' \<leadsto> s'] \<parallel> ([z'' \<leadsto> z''] \<parallel> A) oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            by (simp add: par_assoc par_switch)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> s @ x' @ z] oo [s' \<leadsto> s'] \<parallel> [x' @ z'' \<leadsto> z'' @ x']) oo [s' \<leadsto> s'] \<parallel> ([z'' \<leadsto> z''] \<parallel> A) oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''] oo C'"
            apply (subst switch_par_comp_Subst, simp_all)
            by (simp add: Subst_append Subst_not_in_a Subst_not_in Int_commute)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> s @ x' @ z] oo ([s' \<leadsto> s'] \<parallel> [x' @ z'' \<leadsto> z'' @ x'] oo [s' \<leadsto> s'] \<parallel> ([z'' \<leadsto> z''] \<parallel> A) oo [s' \<leadsto> s'] \<parallel> [z'' @ v \<leadsto> v @ z''])) oo C'"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> s @ x' @ z] oo [s' \<leadsto> s'] \<parallel> ([x' @ z'' \<leadsto> z'' @ x'] oo [z'' \<leadsto> z''] \<parallel> A oo [z'' @ v \<leadsto> v @ z''])) oo C'"
            by (simp add: comp_parallel_distrib  )
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> s @ x' @ z] oo [s' \<leadsto> s'] \<parallel> (A \<parallel> [z'' \<leadsto> z''])) oo C'"
            by (cut_tac T="[z'' \<leadsto> z'']" and S=A and x=x' and y=z'' and u=z'' and v=v in switch_par, simp_all)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> s @ x' @ z] oo [s' \<leadsto> s'] \<parallel> (A \<parallel> [z' \<leadsto> z'])) oo C'"
            apply (simp only: z''_def) 
            by (subst switch_newvars, simp_all)
          also have "... = [u \<leadsto> u @ x] oo ([u @ x' \<leadsto> s @ x' @ z] oo [s' \<leadsto> s'] \<parallel> A \<parallel> [z' \<leadsto> z']) oo C'"
            by (simp add: par_assoc)
          also have "... = ([u \<leadsto> u @ x] oo [u @ x' \<leadsto> s @ x' @ z]) oo ([s' \<leadsto> s'] \<parallel> A \<parallel> [z' \<leadsto> z']) oo C'"
            by (simp add: comp_assoc  )
          also have "... = [u \<leadsto> s @ x @ z] oo ([s' \<leadsto> s'] \<parallel> A \<parallel> [z' \<leadsto> z']) oo C'"
            apply (subst switch_comp_subst, simp_all)
            by (simp add: Subst_append Subst_not_in Subst_not_in_a Subst_eq)

          finally show ?thesis
            by simp
        qed

    lemma length_TVs: "length (TVs x) = length x"
        by (induction x, simp_all)

      lemma comp_par: "distinct x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> [x \<leadsto> x @ x] oo [x \<leadsto> y] \<parallel> [x \<leadsto> y] = [x \<leadsto> y @ y]"
        by (subst switch_par_comp_Subst, simp_all add: set_addvars Subst_eq)

      lemma Subst_switch_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> TVs x = TVs y \<Longrightarrow> [x \<leadsto> z] = [y \<leadsto> Subst x y z]"
        by (metis distinct_id order_refl switch_comp_a switch_comp_subst)

       lemma change_var_names: "distinct a \<Longrightarrow> distinct b \<Longrightarrow> TVs a = TVs b \<Longrightarrow> [a \<leadsto> a @ a] = [b \<leadsto> b @ b]"
         by (simp add: Switch_Split)
           
subsection{*Deterministic diagrams*}
             
definition "deterministic S = (Split (TI S) oo S \<parallel> S = S oo Split (TO S))"
  
lemma deterministic_split:
  assumes "deterministic S"
    and "distinct (a#x)"
    and "TO S = TVs (a # x)"
  shows "S = Split (TI S) oo (S oo [ a # x \<leadsto> [a] ]) \<parallel> (S oo [ a # x \<leadsto> x ])"
proof -
  have A: "[a # x \<leadsto> (a # x) @ a # x] oo [a # x \<leadsto> [a]] \<parallel> [a # x \<leadsto> x] = [a # x \<leadsto> a # x]"
    by (metis Switch_Split append_Cons append_Nil assms(2) switch_append)
  have "Split (TI S) oo (S oo [ a # x \<leadsto> [a] ]) \<parallel> (S oo [ a # x \<leadsto> x ]) = Split (TI S) oo (S \<parallel> S  oo [ a # x \<leadsto> [a] ] \<parallel> [ a # x \<leadsto> x ])"
    by (simp add: assms(3) comp_parallel_distrib)
  also have "... = (Split (TI S) oo S \<parallel> S)  oo [ a # x \<leadsto> [a] ] \<parallel> [ a # x \<leadsto> x ]"
    by (simp add: assms(3) local.comp_assoc)
  also have "... = (S oo Split (TO S))  oo [ a # x \<leadsto> [a] ] \<parallel> [ a # x \<leadsto> x ]"
    using assms(1) deterministic_def by auto
  also have "... = S oo (Split (TO S)  oo [ a # x \<leadsto> [a] ] \<parallel> [ a # x \<leadsto> x ])"
    by (simp add: assms(3) local.comp_assoc)
  also have "... = S oo ([a # x \<leadsto> (a # x) @ (a # x)]  oo [ a # x \<leadsto> [a] ] \<parallel> [ a # x \<leadsto> x ])"
    using Switch_Split assms(2) assms(3) by presburger
  also have "... = S oo [a # x \<leadsto> a # x]"
    by (subst A, simp)
  also have "... = S"
    using assms(2) assms(3) by auto
  finally show ?thesis by simp
qed

lemma deterministicE: "deterministic A \<Longrightarrow> distinct x \<Longrightarrow> distinct y \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs y 
  \<Longrightarrow> [x \<leadsto> x @ x] oo (A \<parallel> A) = A oo [y \<leadsto> y @ y]"
  by (simp add: deterministic_def Switch_Split)

lemma deterministicI: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs y \<Longrightarrow> 
  [x \<leadsto> x @ x] oo A \<parallel> A = A oo [y \<leadsto> y @ y] \<Longrightarrow> deterministic A"
  by (simp add: deterministic_def Switch_Split)
    
lemma deterministic_switch: "distinct x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> deterministic [x \<leadsto> y]"
  by (simp add: deterministic_def switch_dup)


lemma deterministic_comp: "deterministic A \<Longrightarrow> deterministic B \<Longrightarrow> TO A = TI B \<Longrightarrow> deterministic (A oo B)"
proof (simp add: deterministic_def) 
  assume [simp]: "Split (TI A) oo A \<parallel> A = A oo Split (TI B)"
  assume [simp]: "Split (TI B) oo B \<parallel> B = B oo Split (TO B)"
  assume [simp]: "TO A = TI B"

  have " A oo B oo Split (TO B) =
            A oo (B oo Split (TO B))"
    by (subst comp_assoc, simp_all)
  also have "... = A oo (Split (TI B) oo B \<parallel> B)"
    by simp
  also have "... = (A oo Split (TI B)) oo B \<parallel> B"
    by (subst comp_assoc, simp_all)
  also have "... = (Split (TI A) oo A \<parallel> A) oo B \<parallel> B"
    by simp
  also have "... = Split (TI A)  oo (A \<parallel> A oo B \<parallel> B)"
    by (subst comp_assoc, simp_all)
  also have "... = Split (TI A) oo (A oo B) \<parallel> (A oo B)"
    by (simp add: comp_parallel_distrib)
  
  finally show "Split (TI A) oo (A oo B) \<parallel> (A oo B) =  A oo B oo Split (TO B)"
    by simp
qed

lemma deterministic_par: "deterministic A \<Longrightarrow> deterministic B \<Longrightarrow> deterministic (A \<parallel> B)"
proof (simp add: deterministic_def)            
  assume [simp]: "Split (TI A) oo A \<parallel> A = A oo Split (TO A)"
  assume [simp]: "Split (TI B) oo B \<parallel> B = B oo Split (TO B)"

  have [simp]: "Split (TI A) \<parallel> Split (TI B) oo ID (TI A) \<parallel> ID (TI A @ TI B) \<parallel> ID (TI B) = Split (TI A) \<parallel> Split (TI B)"
    proof -
      have "TO (Split (TI A) \<parallel> Split (TI B)) = (TI A @ TI A) @ TI B @ TI B"
        by simp
      then show "Split (TI A) \<parallel> Split (TI B) oo ID (TI A) \<parallel> ID (TI A @ TI B) \<parallel> ID (TI B) = Split (TI A) \<parallel> Split (TI B)"
        by (metis (no_types) append_assoc comp_id_right parallel_ID_sym)
    qed

  have "Split (TI A @ TI B) oo A \<parallel> B \<parallel> (A \<parallel> B) = Split (TI A @ TI B) oo A \<parallel> (B \<parallel> A) \<parallel> B"
    by (simp add: par_assoc)
  also have "... = Split (TI A @ TI B) oo A \<parallel> (Switch (TI B) (TI A) oo A \<parallel> B oo Switch (TO A) (TO B)) \<parallel> B"
    by (subst (2) switch_par_no_vars[THEN sym], simp_all)
  also have "... =  Split (TI A @ TI B) oo ID (TI A) \<parallel> Switch (TI B) (TI A) \<parallel> ID (TI B) oo A \<parallel> (A \<parallel> B) \<parallel> B oo  ID (TO A) \<parallel> Switch (TO A) (TO B) \<parallel> ID (TO B)"
    by (simp add: comp_assoc comp_parallel_distrib)
  also have "... =  Split (TI A) \<parallel> Split (TI B) oo (ID (TI A) \<parallel> Switch (TI A) (TI B) \<parallel> ID (TI B) oo ID (TI A) \<parallel> Switch (TI B) (TI A) \<parallel> ID (TI B)) oo A \<parallel> (A \<parallel> B) \<parallel> B oo  ID (TO A) \<parallel> Switch (TO A) (TO B) \<parallel> ID (TO B)"
    by (simp add: Split_append comp_assoc)
  also have "... =  Split (TI A) \<parallel> Split (TI B) oo  A \<parallel> (A \<parallel> B) \<parallel> B oo  ID (TO A) \<parallel> Switch (TO A) (TO B) \<parallel> ID (TO B)"
    by (simp add: comp_parallel_distrib)
  also have "... =  Split (TI A) \<parallel> Split (TI B) oo  (A \<parallel> A) \<parallel> (B \<parallel> B) oo  ID (TO A) \<parallel> Switch (TO A) (TO B) \<parallel> ID (TO B)"
    by (simp add: par_assoc)
  also have "... = A \<parallel> B oo Split (TO A) \<parallel> Split (TO B) oo ID (TO A) \<parallel> Switch (TO A) (TO B) \<parallel> ID (TO B)"
    by (simp add: comp_parallel_distrib)
  also have "... = A \<parallel> B oo Split (TO A @ TO B)"
    by (simp add: Split_append comp_assoc)

  finally show "Split (TI A @ TI B) oo A \<parallel> B \<parallel> (A \<parallel> B) =  A \<parallel> B oo Split (TO A @ TO B)"
    by simp
qed
  
  
end
  
end
