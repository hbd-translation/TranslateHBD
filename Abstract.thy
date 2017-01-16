theory Abstract imports AbstractOperations
begin

  lemma [simp]: "(X \<inter> (Y \<union> Z) = {}) = (X \<inter> Y = {} \<and> X \<inter> Z = {})"
    by auto

  context BaseOperationVars
    begin
      declare TVs_append [simp]

      lemma [simp]: "distinct x \<Longrightarrow> TVs x = TI A \<Longrightarrow> [x \<leadsto> x] oo A = A"
        by (simp add: distinct_id)

      lemma [simp]: "distinct x \<Longrightarrow> TVs x = TO A \<Longrightarrow> A oo [x \<leadsto> x] = A"
        by (simp add: distinct_id)

      lemma  switch_comp: "distinct x \<Longrightarrow> perm x y \<Longrightarrow> set z \<subseteq> set y \<Longrightarrow> [x\<leadsto>y] oo [y\<leadsto>z] = [x\<leadsto>z]"
        apply (subgoal_tac "distinct y")
        apply (subst switch_comp_subst, simp_all add: Subst_eq)
        apply (simp add: perm_set_eq)
        using dist_perm by blast

      lemma  switch_comp_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set y \<Longrightarrow>[x\<leadsto>y] oo [y\<leadsto>z] = [x\<leadsto>z]"
        by (subst switch_comp_subst, simp_all add: Subst_eq)

      lemma fb_switch_a: "\<And> S . distinct (a # z @ x) \<Longrightarrow> distinct (a # z @ y) \<Longrightarrow> TI S = TVs (z @ a # x) \<Longrightarrow> TO S = TVs (z @ a # y) 
      \<Longrightarrow> (fb ^^ (Suc (length z))) ([a # z @ x \<leadsto> z @ a # x] oo S oo [z @ a # y \<leadsto> a # z @ y]) = (fb ^^ (Suc (length z))) S"
      proof (induction z)
        case Nil
          from Nil show ?case
            by simp_all
      next
        case (Cons b z)
          thm Cons(1)
          thm Cons(2)
          thm Cons(3)
          thm Cons(4)
          thm Cons(5)
          thm fb_twice_switch

        have "(fb ^^ Suc (length (b # z))) ([a # (b # z) @ x \<leadsto> (b # z) @ a # x] oo S oo [(b # z) @ a # y \<leadsto> a # (b # z) @ y]) 
            = (fb ^^ length z) ((fb ^^ (2::nat)) ([a # b # z @ x \<leadsto> b # z @ a # x] oo S oo [b # z @ a # y \<leadsto> a # b # z @ y]))"
          by (simp add: funpow_swap1 numeral_2_eq_2)
        also have "... = (fb ^^ length z) ((fb ^^ 2) ([b # a # z @ x \<leadsto> a # b # z @ x] oo ([a # b # z @ x \<leadsto> b # z @ a # x] oo S oo [b # z @ a # y \<leadsto> a # b # z @ y]) oo [a # b # z @ y \<leadsto> b # a # z @ y]))"
          using Cons by (subst fb_twice_switch, simp_all, auto)

        also have "... = (fb ^^ length z) ((fb ^^ 2) ([b # a # z @ x \<leadsto> b # z @ a # x] oo S oo [b # z @ a # y \<leadsto> b # a # z @ y]))"
          using Cons(4) Cons(5) apply (simp add: comp_assoc [THEN sym])
          using Cons(2) apply (subst switch_comp_a, auto)
          apply (simp add: comp_assoc)
          using Cons by (subst switch_comp_a, auto)
        also have "... = (fb ^^ length z) ((fb ^^ 2) ([[b] \<leadsto> [b]] \<parallel> [a # z @ x \<leadsto> z @ a # x] oo S oo [[b] \<leadsto> [b]] \<parallel> [z @ a # y \<leadsto> a # z @ y]))"
          using Cons by (subst par_switch, auto, subst par_switch, auto)
        also have "... = (fb ^^ length z) (fb (fb ([[b] \<leadsto> [b]] \<parallel> [a # z @ x \<leadsto> z @ a # x] oo S oo [[b] \<leadsto> [b]] \<parallel> [z @ a # y \<leadsto> a # z @ y])))"
          by (simp add: numeral_2_eq_2)
        also have "... = (fb ^^ length z) (fb ([a # z @ x \<leadsto> z @ a # x] oo fb S oo  [z @ a # y \<leadsto> a # z @ y]))"
          apply (simp add: distinct_id TVs_def)
          using Cons(4) Cons(5) by (subst fb_comp, simp_all add: fbtype_def TVs_def)
        also have "... = (fb ^^ Suc (length z)) ([a # z @ x \<leadsto> z @ a # x] oo fb S oo  [z @ a # y \<leadsto> a # z @ y])"
          by (simp add: funpow_add funpow_swap1)
        also have "... = (fb ^^ Suc (length z))  (fb S)"
          using Cons by (subst Cons(1), simp_all add: TI_fb_fbtype TO_fb_fbtype fbtype_def TVs_def)
        also have "... = (fb ^^ Suc (length (a # z))) S"
          by (simp add: funpow_add funpow_swap1)
        finally show ?case by simp
      qed


      (* new *)
      lemma swap_fb: "(fb ^^ length u) ((fb ^^ length v) S) = (fb ^^ length v) ((fb ^^ length u) S)"
        by (metis add.left_commute funpow_add funpow_simps_right(1) o_apply o_id)

      lemma fb_switch_b: "\<And> v x y S . distinct (u @ v @ x) \<Longrightarrow> distinct (u @ v @ y) \<Longrightarrow> TI S = TVs (v @ u @ x) \<Longrightarrow> TO S = TVs (v @ u @ y) 
      \<Longrightarrow> (fb ^^ (length (u @ v))) ([u @ v @ x \<leadsto> v @ u @ x] oo S oo [v @ u @ y \<leadsto> u @ v @ y]) = (fb ^^ (length (u @ v))) S"
        proof (induction u)
        case Nil
          show ?case
            using Nil by simp_all
        next
        case (Cons a u)
          thm Cons(1)
          thm Cons(2)
          thm Cons(3)
          thm Cons(4)
          thm Cons(5)

          have "(fb ^^ length (a # u @ v)) ([a # u @ v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # u @ v @ y])
              =  (fb ^^ length v) ((fb ^^ (Suc (length u)))([a # u @ v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # u @ v @ y]))"
            apply (simp add: funpow_add funpow_swap1)
            by (rule swap_fb)
          also have "... = (fb ^^ length v) ((fb ^^ (Suc (length u))) (
            [a # u @ v @ x \<leadsto> u @ a # v @ x] oo ([u @ a # v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> u @ a # v @ y]) oo [u @ a # v @ y \<leadsto> a # u @ v @ y]))"
            using Cons apply (simp add: comp_assoc switch_comp_a)
            apply (subst switch_comp_a, simp_all, auto)
            apply (simp add: comp_assoc [THEN sym])
            by (subst switch_comp_a, auto)

          also have "... = (fb ^^ length v) ((fb ^^ Suc (length u)) ([u @ a # v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> u @ a # v @ y]))"
            using Cons by (subst fb_switch_a, simp_all)

          also have "... = (fb ^^ (length (u @ (a # v)))) ([u @ a # v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> u @ a # v @ y])"
            apply (simp add: funpow_add funpow_swap1)
            by (rule swap_fb)
          also have "... =  (fb ^^ (length (u @ (a # v)))) ([u @ (a # v) @ x \<leadsto> (a # v) @ u @ x] 
              oo ([(a # v) @ u @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> (a # v) @ u @ y])
              oo [(a # v) @ u @ y \<leadsto> u @ (a # v) @ y])"
            using Cons(4) Cons(5)
            apply (simp add: comp_assoc)
            using Cons(3) apply (subst switch_comp_a, simp_all, auto)
            apply (simp add: comp_assoc [THEN sym])
            using Cons(2) by (subst switch_comp_a, simp_all, auto)

          also have "... = (fb ^^ length (u @ a # v)) ([a # v @ u @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # v @ u @ y])"
            using Cons by (subst Cons(1), simp_all)
          also have "... = (fb ^^ length u) (((fb ^^ (Suc (length v)))) ([a # v @ u @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # v @ u @ y]))"
            by (simp add: funpow_add funpow_swap1)
          also have "... =  (fb ^^ length u) ((fb ^^ Suc (length v)) S)"
            using Cons by (subst fb_switch_a, auto)
          also have "... = (fb ^^ length ((a # u) @ v)) S"
            by (simp add: funpow_add funpow_swap1)
 
          finally show ?case
            by simp
      qed

    lemma perm_empty[simp]: "(perm [] v) = (v = [])" and "(perm v []) = (v = [])"
      by (simp_all add: perm_def)

      lemma split_perm: "perm (a # x) x' = (\<exists> y y' . x' = y @ a # y' \<and> perm x (y @ y'))"
        apply safe
        apply (subgoal_tac "\<exists> y y' .  x' = y @ a # y'")
        apply safe
        apply (rule_tac x = y in exI)
        apply (rule_tac x = y' in exI, simp_all)
          apply (simp add: perm_def)
        apply (drule perm_set_eq)
        apply (simp add: set_eq_iff)
        using split_list apply fastforce
          by (simp add: perm_def)



    lemma fb_perm: "\<And> v S . perm u v \<Longrightarrow> distinct (u @ x) \<Longrightarrow> distinct (u @ y) \<Longrightarrow> fbtype S (TVs u) (TVs x) (TVs y) 
        \<Longrightarrow> (fb ^^ (length u)) ([v @ x \<leadsto> u @ x] oo S oo [u @ y \<leadsto> v @ y]) = (fb ^^ (length u)) S"
      proof (induction u)
        case Nil
          show ?case
            using Nil by (simp add: fbtype_def TVs_def)
        next
        case (Cons a u)
          from \<open>perm (a # u) v\<close> obtain w w' where "v = w @ a # w'" and [simp]: "perm u (w @ w')"
            by (simp add: split_perm, blast)

          have [simp]: "length u = length w + length w'"
            using \<open>perm u (w @ w')\<close> perm_length by fastforce

          have [simp]: "set u = set w \<union> set w'"
            using \<open>perm u (w @ w')\<close> perm_set_eq by fastforce

          have [simp]: "distinct w" and [simp]:"distinct w'"
            apply (meson Cons.prems(3) \<open>perm u (w @ w')\<close> dist_perm distinct.simps(2) distinct_append)
            by (meson Cons.prems(3) \<open>perm u (w @ w')\<close> dist_perm distinct.simps(2) distinct_append)

          have A: "set w \<inter> set w' = {}"
            by (meson Cons.prems(3) \<open>perm u (w @ w')\<close> dist_perm distinct.simps(2) distinct_append)

          have "(fb ^^ length (a # u)) ([v @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> v @ y]) 
            = (fb ^^ length w') ((fb ^^ (length (w @ [a]))) ([w @ a # w' @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> w @ a # w' @ y]))"
            apply (simp add: funpow_add funpow_swap1)
            using \<open>v = w @ a # w'\<close> swap_fb by fastforce
          thm fb_switch_a
          thm fb_switch_b
          thm fbtype_def
          also have "... = (fb ^^ length w') ((fb ^^ (length (w @ [a]))) ([w @ [a] @ w' @ x \<leadsto> [a] @ w @ w' @ x] 
              oo ([[a] @ w @ w' @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto>[a] @ w @ w' @ y])
              oo [[a] @ w @ w' @ y \<leadsto> w @ [a] @ w' @ y]))"
            using A Cons apply (simp add: comp_assoc fbtype_def )
            apply (subst switch_comp_a, auto)
            apply (simp add: comp_assoc [THEN sym] )
            by (subst switch_comp_a, auto)
          also have "... = (fb ^^ length w') ((fb ^^ length (w @ [a])) ([a # w @ w' @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> a # w @ w' @ y]))"
            using A Cons by (subst fb_switch_b, simp_all add: fbtype_def, auto)

          also have "... = (fb ^^ length u) (fb ([a # w @ w' @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> a # w @ w' @ y]))"
            apply (simp add: funpow_add funpow_swap1)
            using \<open>v = w @ a # w'\<close> swap_fb by fastforce
          also have "... = (fb ^^ length u) (fb ([[a] \<leadsto> [a]] \<parallel> [w @ w' @ x \<leadsto> u @ x] oo S oo [[a] \<leadsto> [a]] \<parallel> [u @ y \<leadsto> w @ w' @ y]))"
            using A Cons by (subst par_switch, simp_all add: fbtype_def TVs_def, auto, subst par_switch, auto)
          also have "... = (fb ^^ length u) ([(w @ w') @ x \<leadsto> u @ x] oo fb S oo [u @ y \<leadsto> (w @ w') @ y])"
            using Cons apply (simp add: distinct_id)
            by (subst fb_comp, simp_all add: fbtype_def)

          thm Cons(1)
          also have "... = (fb ^^ length u) (fb S)"
            using A Cons by (subst Cons(1), simp_all add: fbtype_def TI_fb_fbtype TO_fb_fbtype)

          also have "... = (fb ^^ length (a # u)) S"
            by (simp add: funpow_add funpow_swap1)
          finally show ?case
            by (simp)
      qed
        
      (*todo: remove this*)
      lemma type_length: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> TVs x = TVs y \<Longrightarrow> length x = length y"
        by (metis local.TVs_length_eq)


      lemma comp_assoc_middle_ext: "TI S2 = TO S1 \<Longrightarrow> TI S3 = TO S2 \<Longrightarrow> TI S4 = TO S3 \<Longrightarrow> TI S5 = TO S4 \<Longrightarrow>
          S1 oo (S2 oo S3 oo S4) oo S5 = (S1 oo S2) oo S3 oo (S4 oo S5)"
        by (simp add: comp_assoc)

      
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


      lemma par_empty_right: "A \<parallel> [[] \<leadsto> []] = A"
        by (simp add: distinct_id)

      lemma par_empty_left: "[[] \<leadsto> []] \<parallel> A = A"
        by (simp add: distinct_id)


      lemma Subst_cons: "distinct x \<Longrightarrow> a \<notin> set x \<Longrightarrow> b \<notin> set x \<Longrightarrow> length x = length y\<Longrightarrow>  Subst (a # x) (b # y) z = Subst x y (Subst [a] [b] z)"
        by (induction z, simp_all)


      lemma "Subst [1::nat, 2, 3, 4] [2,1,4,2] [3,1,2,4,4,4,2,3] = [4,2,1,2,2,2,1,4]"
         by simp

      lemma  distinct_vars_comp: "distinct x \<Longrightarrow> perm x y \<Longrightarrow> [x\<leadsto>y] oo [y\<leadsto>x] = ID (TVs x)"
        by (simp add: switch_comp distinct_id perm_set_eq)

      lemma comp_id_right_a: "TO S = ts \<Longrightarrow> S oo ID ts = S"
        using comp_id_right by blast

      lemma comp_id_left_a: "TI S = ts \<Longrightarrow> ID ts oo S  = S"
        using comp_id_left by blast

      lemma comp_switch_id[simp]: "distinct x \<Longrightarrow> TO S = TVs x \<Longrightarrow> S oo [x \<leadsto> x] = S"
        by (simp add: distinct_id)

      lemma comp_id_switch[simp]: "distinct x \<Longrightarrow> TI S = TVs x \<Longrightarrow> [x \<leadsto> x] oo S = S "
        by (simp add: distinct_id)

      
      thm comp_id_left

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

      lemma Subst_switch_more_general: "distinct u \<Longrightarrow> distinct (v @ x) \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> TVs u = TVs v \<Longrightarrow> [x \<leadsto> y] = [Subst u v x \<leadsto> Subst u v y]"
        proof -
          assume [simp]: "distinct u"
          assume [simp]: "set y \<subseteq> set x"
          assume [simp]: " TVs u = TVs v"
          assume "distinct (v @ x)"
          from this have [simp]: "distinct v" and [simp]: "distinct x" and [simp]: "set v \<inter> set x = {}"
            by simp_all

          have [simp]: "length u = length v"
            by (simp add: type_length)

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


      lemma fb_gen_serial: "\<And>A B v x . distinct (u @ v @ x) \<Longrightarrow> TO A = TVs (v@x) \<Longrightarrow> TI B = TVs (u @ x) \<Longrightarrow>  TVs u = TVs v \<Longrightarrow> (fb ^^ length u) (([u \<leadsto> u] \<parallel> A) oo [u @ v @ x \<leadsto> v @ u @ x] oo ([v \<leadsto> v] \<parallel> B)) = A oo B"
        apply (induction u, simp)
        apply (simp add: distinct_id)
        apply simp
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
            by (unfold inf_set_def, auto)
          assume [simp]:"set u \<inter> set x = {}"

          have [simp]: "length v' = length u"
            by (simp add: type_length)

          have [simp]: "perm (a # u @ b # v' @ x) (a # b # v' @ u @ x)"
            by (simp add: perm_def )
          have [simp]: "perm (a # u @ b # v' @ x) (b # a # v' @ u @ x)"
            by (simp add: perm_def )

          have [simp]:"perm (u @ b # v' @ x) (u @ v' @ b # x)"
            by (simp add: perm_def )

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
                by (simp add: perm_def union_assoc union_lcomm)
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
                by (simp add: perm_def union_assoc union_lcomm)
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
                by (simp add: perm_def union_assoc union_lcomm)
            qed

          assume ind_hyp: "(\<And>A B v x. distinct v \<and> distinct x \<and> set v \<inter> set x = {} \<and> set u \<inter> set v = {} \<and> set u \<inter> set x = {} \<Longrightarrow>
                   TO A = TVs v @ TVs x \<Longrightarrow> TI B = TVs v @ TVs x \<Longrightarrow> TVs v' = TVs v \<Longrightarrow> (fb ^^ length u) ([u \<leadsto> u] \<parallel> A oo [u @ v @ x \<leadsto> v @ u @ x] oo [v \<leadsto> v] \<parallel> B) = A oo B)"

          def A' \<equiv> "[u\<leadsto> u] \<parallel> A oo [u@b#v'@x \<leadsto> b#v'@u@x]"
          def B' \<equiv> "[a#v'@u@x \<leadsto> v'@a#u@x] oo [v'\<leadsto> v'] \<parallel> B"

          def A'' \<equiv> "A oo [b#v'@x \<leadsto> v'@b#x]"
          def B'' \<equiv> "[u@a#x \<leadsto> a#u@x] oo B"

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
        
        declare parallel_ID [simp del]

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
              apply (subst comp_id_left_a)
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
              apply (subst comp_id_left_a)
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
              apply (subst comp_id_right_a)
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
              apply (subst comp_id_right_a)
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


      thm newvars_old_distinct

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
            apply (cut_tac A, simp_all, auto)
            by (simp add: v_def)

          have F: "distinct ((v @ y @ u) @ x')"
            apply (cut_tac x = "u @ x @ x' @ y" and ts = "TVs u" in newvars_old_distinct)
            apply (unfold v_def [THEN symmetric])
            apply (cut_tac A, simp_all, auto)
            by (simp add: v_def)

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
            apply (simp add: perm_def)
            by auto

          thm switch_par

         also have "... = ([u @ x @ x' \<leadsto> x @ u @ x'] oo (A \<parallel> [u @ x' \<leadsto> u @ x']) oo [v @ y @ u @ x' \<leadsto> u @ v @ y @ x']) oo  [u @ v @ y @ x' \<leadsto> v @ y @ u @ x'] oo [v @ y \<leadsto> v @ y] \<parallel> B"
          apply (subgoal_tac "[u \<leadsto> u] \<parallel> (A \<parallel> [x' \<leadsto> x']) = [u @ x @ x' \<leadsto> x @ u @ x'] oo A \<parallel> [u @ x' \<leadsto> u @ x'] oo [v @ y @ u @ x' \<leadsto> u @ v @ y @ x']", simp_all)
          apply (subst par_assoc [THEN sym])
          apply (subst switch_par [of "u" "x" "v @ y" "u"])
          apply (cut_tac E, simp)
          apply (cut_tac B)
          apply auto [1]
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
          apply (simp add: add.left_commute perm_def)
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

    end


  record ('var, 'a) Dgr =
    In:: "'var list"
    Out:: "'var list"
    Trs:: 'a


  context BaseOperationVars 
    begin

      definition "Var A B = (Out A) \<otimes> (In B) "

      definition "type_ok A = (TVs (In A) = TI (Trs A) \<and> TVs (Out A) = TO (Trs A) \<and> distinct (In A) \<and> distinct (Out A))"


      definition  Comp :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr"  (infixl ";;" 70) where
        "A ;; B = (let I = In B \<ominus> Var A B in let O' = Out A \<ominus> Var A B in
          \<lparr>In = (In A) \<oplus> I, Out = O' @ Out B, Trs = [(In A) \<oplus> I \<leadsto> In A @ I ] oo Trs A \<parallel> [I \<leadsto> I] oo [Out A @ I \<leadsto> O' @ In B]  oo ([O' \<leadsto> O'] \<parallel> Trs B) \<rparr>)"

      lemma type_ok_Comp_a: "type_ok A \<Longrightarrow> type_ok B 
        \<Longrightarrow> set (Out A \<ominus> In B) \<inter> set (Out B) = {} \<Longrightarrow> type_ok (A ;; B)"
        apply (simp add: type_ok_def Comp_def Let_def Var_def, safe)
        using TI_comp TO_comp   apply auto
        apply (simp add: addvars_def)
        apply (simp add: distinct_diff set_diff)
        apply (simp add: distinct_diff set_diff)
        by (simp add: set_diff set_inter, auto)

      (*to replace this with the above one*)
      lemma type_ok_Comp: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> type_ok (A ;; B)"
        by (rule type_ok_Comp_a, simp_all add: set_diff, auto)

    

      lemma Comp_in_disjoint: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (In A) \<inter> set (In B) = {} \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> 
          A ;; B = (let I = diff (In B) (Var A B) in let O' = diff (Out A) (Var A B) in
          \<lparr>In = (In A) @ I, Out = O' @ Out B, Trs = Trs A \<parallel> [I \<leadsto> I] oo [Out A @ I \<leadsto> O' @ In B]  oo ([O' \<leadsto> O'] \<parallel> Trs B) \<rparr>)"
        apply (simp add: Comp_def Let_def Var_def type_ok_def, safe)
        apply (simp add: Diff_Int_distrib addvars_distinct set_diff)
        apply (subgoal_tac "In A \<oplus> (In B \<ominus> Out A \<otimes> In B) = In A @ (In B \<ominus> Out A \<otimes> In B)")
        apply simp
        apply (subst distinct_id)
        apply (simp add: Diff_Int_distrib distinct_diff set_diff)
        apply (cut_tac S="Trs A \<parallel> [In B \<ominus> Out A \<otimes> In B \<leadsto> In B \<ominus> Out A \<otimes> In B]" in comp_id_left)
        apply simp      
        by (simp add: Diff_Int_distrib addvars_distinct set_diff)


      lemma Comp_full: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> Out A = In B \<Longrightarrow>
          A ;; B = \<lparr>In = In A, Out = Out B, Trs = Trs A oo Trs B \<rparr>"
        apply (simp add: Comp_def Let_def Var_def type_ok_def, safe)
        apply (simp add: diff_inter_left diff_eq addvars_def)
        apply (simp add: diff_inter_left diff_eq addvars_def)
        apply (simp add: diff_inter_left diff_eq addvars_def)
        by (simp add: par_empty_left par_empty_right)


      lemma Comp_in_out: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (Out A) \<subseteq> set (In B) \<Longrightarrow>
          A ;; B = (let I = diff (In B) (Var A B) in let O' = diff (Out A) (Var A B) in
          \<lparr>In = In A \<oplus> I, Out = Out B, Trs = [In A \<oplus> I \<leadsto> In A @ I ] oo Trs A \<parallel> [I \<leadsto> I] oo [Out A @ I \<leadsto> In B] oo Trs B \<rparr>)"
        by (simp add: Comp_def Let_def Var_def diff_inter_left diff_inter_right diff_subset par_empty_left)


      thm type_ok_Comp_a

      (*todo: move to variable section*)
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
            by (simp add: type_length)

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
            
      (*move to variable section*)
      lemma switch_par_comp: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> distinct z \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x 
        \<Longrightarrow> set y' \<subseteq> set y \<Longrightarrow> set z' \<subseteq> set z \<Longrightarrow> [x \<leadsto> y @ z] oo [y \<leadsto> y'] \<parallel> [z \<leadsto> z'] = [x \<leadsto> y' @ z']"
        by (subst switch_par_comp_Subst, simp_all add: Subst_eq)

      (*move to variable section*)
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

      thm spec
      thm exI

      (*move to variable section*)

      lemma paralle_switch: "\<exists> x y u v. distinct (x @ y) \<and> distinct (u @ v) \<and> TVs x = TI A 
        \<and> TVs u = TO A \<and> TVs y = TI B \<and> 
        TVs v = TO B \<and> A \<parallel> B = [x @ y \<leadsto> y @ x] oo (B \<parallel> A) oo [v @ u \<leadsto> u @ v]"
        apply (rule_tac x="newvars [] (TI A)" in exI)
        apply (rule_tac x="newvars (newvars [] (TI A)) (TI B)" in exI)
        apply (rule_tac x="newvars [] (TO A)" in exI)
        apply (rule_tac x="newvars (newvars [] (TO A)) (TO B)" in exI)
        by (subst switch_par, simp_all)

      (*move to variable section*)

      lemma par_switch_eq_dist: "distinct (u @ v) \<Longrightarrow> distinct y' \<Longrightarrow> distinct z' \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs v \<Longrightarrow> TI C = TVs v @ TVs y \<Longrightarrow> TVs y = TVs y' \<Longrightarrow>
            TI C' = TVs v @ TVs z \<Longrightarrow> TVs z = TVs z' \<Longrightarrow>
            set x \<subseteq> set u \<Longrightarrow> set y \<subseteq> set u \<Longrightarrow> set z \<subseteq> set u \<Longrightarrow> 
            [v @ u \<leadsto> v @ y] oo C = [v @ u \<leadsto> v @ z] oo C' \<Longrightarrow> [u \<leadsto> x @ y] oo ( A \<parallel> [y' \<leadsto> y']) oo C = [u \<leadsto> x @ z] oo ( A \<parallel> [z' \<leadsto> z']) oo C'"  
        apply (rule  par_switch_eq, simp_all)
        by (simp add: par_switch Int_commute)

     (*move to variable section*)

      lemma par_switch_eq_dist_a: "distinct (u @ v) \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs v \<Longrightarrow> TI C = TVs v @ TVs y \<Longrightarrow> TVs y = ty \<Longrightarrow> TVs z = tz \<Longrightarrow>
            TI C' = TVs v @ TVs z \<Longrightarrow> set x \<subseteq> set u \<Longrightarrow> set y \<subseteq> set u \<Longrightarrow> set z \<subseteq> set u \<Longrightarrow> 
            [v @ u \<leadsto> v @ y] oo C = [v @ u \<leadsto> v @ z] oo C' \<Longrightarrow> [u \<leadsto> x @ y] oo A \<parallel> ID ty oo C = [u \<leadsto> x @ z] oo A \<parallel> ID tz oo C'"
        apply (cut_tac y' = "newvars [] ty" and z' = "newvars [] tz" and C = C 
            and x = x and y = y and z = z in par_switch_eq_dist, simp_all)
        by (simp add: distinct_id)

      (*move to variable section*)

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

          def x' \<equiv> "newvars u (TVs x)"
          def y'' \<equiv> "newvars (x' @ v) (TVs y')"
          def z'' \<equiv> "newvars (x' @ v) (TVs z')"


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


      (*very specialized*)  
      lemma Comp_assoc_new_subst_aux: "set u \<inter> set y \<inter> set z = {} \<Longrightarrow> distinct z \<Longrightarrow> length u = length u' 
        \<Longrightarrow> Subst (z \<ominus> v) (Subst u u' (z \<ominus> v)) z = Subst (u \<ominus> y \<ominus> v) (Subst u u' (u \<ominus> y \<ominus> v)) z"
        apply (induction z, simp_all, auto)
        apply (subst subst_notin)
        apply (simp_all add: set_diff)
        apply (case_tac "a \<in> set u", simp_all)
        apply (cut_tac z = "[a]" in Subst_Subst [of u u' _ "(u \<ominus> y \<ominus> v)"], simp_all)
        by (simp_all add: set_diff)


      lemma Comp_assoc_new: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow>
          set (Out A \<ominus> In B) \<inter> set (Out B) = {} \<Longrightarrow>  set (Out A \<otimes> In B) \<inter> set (In C) = {} 
          \<Longrightarrow> (* set ((Out A \<ominus> In B) @ Out B \<ominus> In C) \<inter> set (Out C) = {} \<Longrightarrow> *)
          A ;; B ;; C = A ;; (B ;; C)"
          proof -
            assume [simp]: "type_ok A"
            assume [simp]: "type_ok B"
            assume [simp]: "type_ok C"
            assume U: "set (Out A \<ominus> In B) \<inter> set (Out B) = {}"
            assume V: " set (Out A \<otimes> In B) \<inter> set (In C) = {}"
            have A: "In A \<oplus> (In B \<ominus> Out A \<otimes> In B) \<oplus> (In C \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C) = In A \<oplus> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C)))"
             apply (simp add: diff_inter_left diff_inter_right)
             apply (simp add: addvars_def union_diff diff_union diff_cancel)
             apply (subst diff_sym [THEN sym])
             apply (subst (2) diff_sym [THEN sym])
             apply (subst ZZZ_b)
             using V apply (auto simp add: set_inter set_diff) [1]
             by (simp add: diff_sym)

            have B: "((Out A \<ominus> Out A \<otimes> In B) @ Out B \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C) = (Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) @ (Out B \<ominus> Out B \<otimes> In C)"
              using U by (simp add: diff_inter_left diff_inter_right addvars_def union_diff diff_union diff_cancel diff_notin)

          (*assume W: "set ((Out A \<ominus> In B) @ Out B \<ominus> In C) \<inter> set (Out C) = {}"*)

          def x \<equiv> "In A"
          def u \<equiv> "Out A"
          def y \<equiv> "In B"
          def v \<equiv> "Out B"
          def z \<equiv> "In C"
          def w \<equiv> "Out C"

          have [simp]: "TI (Trs A) = TVs x"
            by (metis \<open>type_ok A\<close> type_ok_def x_def)

          have [simp]: "TI (Trs B) = TVs y"
            by (metis \<open>type_ok B\<close> type_ok_def y_def)

          have [simp]: "TO (Trs A) = TVs u"
            by (metis \<open>type_ok A\<close> type_ok_def u_def)

          thm comp_parallel_distrib

          thm comp_id_right_a

          have [simp]: "distinct x"
           by (metis \<open>type_ok A\<close> type_ok_def x_def)

          have [simp]: "distinct u"
           by (metis \<open>type_ok A\<close> type_ok_def u_def)

          have [simp]: "distinct y"
           by (metis \<open>type_ok B\<close> type_ok_def y_def)

          have [simp]: "distinct z"
           by (metis \<open>type_ok C\<close> type_ok_def z_def)

          have [simp]: "distinct (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)"
            by (simp add: distinct_diff)

          have [simp]: "distinct (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))"
            by (simp add: distinct_addvars distinct_diff)

          have [simp]: "distinct (x \<oplus> (y \<ominus> u \<otimes> y))"
            by (simp add: distinct_addvars distinct_diff)

          have [simp]: "set (x \<oplus> (y \<ominus> u \<otimes> y)) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))"
            apply (simp add: set_addvars set_diff set_inter)
            by blast

          have [simp]: "set (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))"
            apply (simp add: diff_inter_left diff_inter_right diff_union addvars_minus set_addvars)
            apply (subgoal_tac "set (z \<ominus> (u \<ominus> y) \<ominus> v) \<subseteq> set (z \<ominus> v \<ominus> u)")
            apply blast
            apply (subst diff_sym)
            apply (simp add: set_diff)
            by (metis diff_cancel_set Int_ac(3) V diff_inter_left eq_iff set_diff u_def y_def z_def)

          have [simp]: "set x \<subseteq> set (x \<oplus> (y \<ominus> u \<otimes> y)) \<and> set (y \<ominus> u \<otimes> y) \<subseteq> set (x \<oplus> (y \<ominus> u \<otimes> y))"
            by (simp add: set_addvars set_diff set_inter)

          have [simp]: "distinct (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))"
            by (simp add: distinct_addvars distinct_diff)
            
          have [simp]: "set u \<inter> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) = {}"
            by (simp add: set_diff set_inter set_addvars, auto)
            
          have [simp]: "distinct (y \<oplus> (z \<ominus> v \<otimes> z))"
            by (simp add: distinct_addvars distinct_diff)
            
          have [simp]: "set (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<subseteq> set u \<union> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))"
            by (simp add: set_diff set_inter set_addvars, auto)
          have [simp]: "set (y \<oplus> (z \<ominus> v \<otimes> z)) \<subseteq> set u \<union> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))"
            by (simp add: set_diff set_inter set_addvars, auto)
          have [simp]: "set y \<subseteq> set (y \<oplus> (z \<ominus> v \<otimes> z))"
            by (simp add: set_diff set_inter set_addvars)
            
          have [simp]: "set (z \<ominus> v \<otimes> z) \<subseteq> set (y \<oplus> (z \<ominus> v \<otimes> z))"
            by (simp add: set_diff set_inter set_addvars)

          have [simp]: "TO (Trs B) = TVs v"
            by (metis \<open>type_ok B\<close> type_ok_def v_def)
          have [simp]: " TI (Trs C) = TVs z"
            by (metis \<open>type_ok C\<close> type_ok_def z_def)

          have "[x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (x \<oplus> (y \<ominus> u \<otimes> y)) @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)] oo
              ([x \<oplus> (y \<ominus> u \<otimes> y) \<leadsto> x @ (y \<ominus> u \<otimes> y)] oo Trs A \<parallel> [y \<ominus> u \<otimes> y \<leadsto> y \<ominus> u \<otimes> y] oo [u @ (y \<ominus> u \<otimes> y) \<leadsto> (u \<ominus> u \<otimes> y) @ y] oo [u \<ominus> u \<otimes> y \<leadsto> u \<ominus> u \<otimes> y] \<parallel> Trs B) \<parallel>
              [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z] oo
              [(u \<ominus> u \<otimes> y) @ v @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) @ z] oo
              [(u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z)] \<parallel> Trs C
              = 
              [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (x \<oplus> (y \<ominus> u \<otimes> y)) @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)] oo
              ([x \<oplus> (y \<ominus> u \<otimes> y) \<leadsto> x @ (y \<ominus> u \<otimes> y)] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo Trs A \<parallel> [y \<ominus> u \<otimes> y \<leadsto> y \<ominus> u \<otimes> y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u @ (y \<ominus> u \<otimes> y) \<leadsto> (u \<ominus> u \<otimes> y) @ y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u \<ominus> u \<otimes> y \<leadsto> u \<ominus> u \<otimes> y] \<parallel> Trs B \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]) oo
              [(u \<ominus> u \<otimes> y) @ v @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) @ z] oo
              [(u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z)] \<parallel> Trs C" (is "?Tx = _")

          apply (subst comp_parallel_distrib, simp_all)
          apply (subst comp_parallel_distrib, simp_all )
          by (subst comp_parallel_distrib, simp_all)
          also have "... = [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (x \<oplus> (y \<ominus> u \<otimes> y)) @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)] oo
              [x \<oplus> (y \<ominus> u \<otimes> y) \<leadsto> x @ (y \<ominus> u \<otimes> y)] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo Trs A \<parallel> [y \<ominus> u \<otimes> y \<leadsto> y \<ominus> u \<otimes> y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u @ (y \<ominus> u \<otimes> y) \<leadsto> (u \<ominus> u \<otimes> y) @ y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u \<ominus> u \<otimes> y \<leadsto> u \<ominus> u \<otimes> y] \<parallel> Trs B \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z] oo
              [(u \<ominus> u \<otimes> y) @ v @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) @ z] oo
              [(u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z)] \<parallel> Trs C"
           by (simp add: comp_assoc )

           also have "... = [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto>x @ (y \<ominus> u \<otimes> y) @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)]
              oo Trs A \<parallel> [y \<ominus> u \<otimes> y \<leadsto> y \<ominus> u \<otimes> y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u @ (y \<ominus> u \<otimes> y) \<leadsto> (u \<ominus> u \<otimes> y) @ y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u \<ominus> u \<otimes> y \<leadsto> u \<ominus> u \<otimes> y] \<parallel> Trs B \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z] oo
              [(u \<ominus> u \<otimes> y) @ v @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) @ z] oo
              [(u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z)] \<parallel> Trs C"
           by (subst switch_par_comp, simp_all)

           also have "... = [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto>x @ (y \<ominus> u \<otimes> y) @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)]
              oo Trs A \<parallel> [y \<ominus> u \<otimes> y \<leadsto> y \<ominus> u \<otimes> y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo ([u @ (y \<ominus> u \<otimes> y) \<leadsto> (u \<ominus> u \<otimes> y) @ y] \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z]
              oo [u \<ominus> u \<otimes> y \<leadsto> u \<ominus> u \<otimes> y] \<parallel> Trs B \<parallel> [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z] oo
              [(u \<ominus> u \<otimes> y) @ v @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) @ z] oo
              [(u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z)] \<parallel> Trs C)" (is "_ = ?Ty")
           by (simp add: comp_assoc  )

          finally have E: "?Tx = ?Ty"
            by simp

          thm comp_parallel_distrib

          have [simp]: "distinct (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) )"
            by (simp add: diff_inter_left diff_inter_right distinct_diff)

          have "[x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> x @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))] 
              oo Trs A \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] oo
              [u @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (y \<oplus> (z \<ominus> v \<otimes> z))] oo
              [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel>
              ([y \<oplus> (z \<ominus> v \<otimes> z) \<leadsto> y @ (z \<ominus> v \<otimes> z)] oo Trs B \<parallel> [z \<ominus> v \<otimes> z \<leadsto> z \<ominus> v \<otimes> z] oo [v @ (z \<ominus> v \<otimes> z) \<leadsto> (v \<ominus> v \<otimes> z) @ z] oo [v \<ominus> v \<otimes> z \<leadsto> v \<ominus> v \<otimes> z] \<parallel> Trs C)
              = 
                [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> x @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))] 
                oo Trs A \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] oo
                [u @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (y \<oplus> (z \<ominus> v \<otimes> z))] oo
                  ([u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<leadsto> y @ (z \<ominus> v \<otimes> z)] oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> (Trs B \<parallel> [z \<ominus> v \<otimes> z \<leadsto> z \<ominus> v \<otimes> z]) oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [v @ (z \<ominus> v \<otimes> z) \<leadsto> (v \<ominus> v \<otimes> z) @ z] oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> ([v \<ominus> v \<otimes> z \<leadsto> v \<ominus> v \<otimes> z] \<parallel> Trs C))" (is "?Ta = _")

          apply (subst comp_parallel_distrib, simp_all)
          apply (subst comp_parallel_distrib, simp_all )
          by (subst comp_parallel_distrib, simp_all )

          also have "... =  [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> x @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))] 
                oo Trs A \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] oo
                  ([u @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (y \<oplus> (z \<ominus> v \<otimes> z))] oo
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<leadsto> y @ (z \<ominus> v \<otimes> z)]) oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> (Trs B \<parallel> [z \<ominus> v \<otimes> z \<leadsto> z \<ominus> v \<otimes> z]) oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [v @ (z \<ominus> v \<otimes> z) \<leadsto> (v \<ominus> v \<otimes> z) @ z] oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> ([v \<ominus> v \<otimes> z \<leadsto> v \<ominus> v \<otimes> z] \<parallel> Trs C)"
           by (simp add: comp_assoc  )

           also have "... = [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> x @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))] 
                oo Trs A \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] oo
                  [u @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (y @ (z \<ominus> v \<otimes> z))] oo
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> (Trs B \<parallel> [z \<ominus> v \<otimes> z \<leadsto> z \<ominus> v \<otimes> z]) oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [v @ (z \<ominus> v \<otimes> z) \<leadsto> (v \<ominus> v \<otimes> z) @ z] oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> ([v \<ominus> v \<otimes> z \<leadsto> v \<ominus> v \<otimes> z] \<parallel> Trs C)"
           by (subst switch_par_comp, simp_all)

           also have "... = [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> x @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))] 
                oo Trs A \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] oo
                  ([u @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (y @ (z \<ominus> v \<otimes> z))] oo
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> Trs B \<parallel> [z \<ominus> v \<otimes> z \<leadsto> z \<ominus> v \<otimes> z] oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [v @ (z \<ominus> v \<otimes> z) \<leadsto> (v \<ominus> v \<otimes> z) @ z] oo 
                  [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel> [v \<ominus> v \<otimes> z \<leadsto> v \<ominus> v \<otimes> z] \<parallel> Trs C)" (is "_ = ?Tb")
           by (simp add: comp_assoc par_assoc  )

          finally have F: "?Ta = ?Tb"
            by simp


          have [simp]: "distinct  (z \<ominus> (u \<ominus> y) @ v)"
            by (metis \<open>distinct (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)\<close> diff_inter_left diff_inter_right)


          def z' \<equiv> "newvars (y \<ominus> u) (TVs (z \<ominus> (u \<ominus> y) @ v))"

          have [simp]: "distinct (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
            by (metis \<open>distinct (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))\<close> diff_inter_right)
          have "distinct (y \<ominus> u)"
            by (simp add: distinct_diff)

          have [simp]: "distinct z'"
            by (simp add: z'_def)

          have [simp]: "set (y \<ominus> u) \<inter> set z' = {}"
            by (simp add: z'_def)

          have [simp]: "distinct (y \<oplus> (z \<ominus> v) \<ominus> u)"
            by (simp add: distinct_diff distinct_addvars)

          have [simp]: "TVs (z \<ominus> (u \<ominus> y) @ v) = TVs z'"
            by (simp add: z'_def)

          have [simp]:"set x \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
            by (simp add: set_diff set_inter set_addvars)
            
          have [simp]:"set (y \<ominus> u) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
            by (simp add: set_diff set_inter set_addvars, auto)
          
          have [simp]:"set (z \<ominus> (u \<ominus> y) @ v) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
            by (metis \<open>set (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))\<close> diff_inter_left diff_inter_right)

          have [simp]:"set (y \<oplus> (z \<ominus> v) \<ominus> u) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
            by (simp add: set_addvars)

          have [simp]: "distinct (y \<ominus> u)"
            by (simp add: distinct_diff)

          have H: "Trs A \<parallel> [y \<ominus> u \<leadsto> y \<ominus> u] \<parallel> [z \<ominus> (u \<ominus> y) @ v \<leadsto> z \<ominus> (u \<ominus> y) @ v] = Trs A \<parallel> [(y \<ominus> u) @ z' \<leadsto> (y \<ominus> u) @ z']"
            by (simp add: par_assoc distinct_id parallel_ID)

          def u' \<equiv> "newvars (x @ y @ z @ v) (TVs u)"

          have b: "set (x @ y @ z @ v) \<inter> set u' = {}"
            by (simp add: u'_def del: set_append)
            

          have [simp]: "distinct u'"
            by (simp add: u'_def)
          from b have [simp]: "set u' \<inter> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) = {}"
            by (simp add: set_addvars set_diff, auto)
          have [simp]: "set u \<inter> set (y \<oplus> (z \<ominus> v) \<ominus> u) = {}"
            by (metis \<open>set u \<inter> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) = {}\<close> diff_inter_right)
          have [simp]: "TVs u' = TVs u"
            by (simp add: u'_def)

 
          have Ha: "[u \<leadsto> u] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> (y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v)] =  [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ ((y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v))]"
            proof -
            have "[u \<leadsto> u] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> (y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v)] = [u' \<leadsto> u'] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> (y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v)]"
              by (simp add: par_assoc distinct_id parallel_ID)
            also have "... = [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ ((y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v))]"
              by (simp add: par_switch)
            finally show ?thesis by simp
            qed
       
          have Hb: "[u \<leadsto> u] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> y \<oplus> (z \<ominus> v) \<ominus> u] = [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ (y \<oplus> (z \<ominus> v) \<ominus> u)]"
            proof -
            have "[u \<leadsto> u] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> y \<oplus> (z \<ominus> v) \<ominus> u] = [u' \<leadsto> u'] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> y \<oplus> (z \<ominus> v) \<ominus> u]"
              by (simp add: par_assoc distinct_id parallel_ID)
            also have "... =  [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ (y \<oplus> (z \<ominus> v) \<ominus> u)]"
              by (simp add: par_switch)
            finally show ?thesis by simp
            qed

         have [simp]: " Subst (z \<ominus> (u \<ominus> y) @ v) (z \<ominus> (u \<ominus> y) @ v) (z \<ominus> (u \<ominus> y) @ v) = (z \<ominus> (u \<ominus> y) @ v)"
          by (simp add: Subst_eq)


          thm Subst_cancel_right

         have [simp]: "Subst (u @ (y \<ominus> u)) (u' @ (y \<ominus> u)) ((u \<ominus> y) @ y) = Subst u u' (u \<ominus> y) @ Subst u u' y"
          apply (simp add: Subst_append, safe)
          apply (subst Subst_cancel_left, simp_all)
          apply (simp add: set_diff)
          apply (simp add: type_length)
          apply (subst Subst_cancel_left, simp_all)
          apply (simp add: set_diff)
          by (simp add: type_length)
        
         have Hc: "[u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ (y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v)] oo [u @ (y \<ominus> u) \<leadsto> (u \<ominus> y) @ y] \<parallel> [z \<ominus> (u \<ominus> y) @ v \<leadsto> z \<ominus> (u \<ominus> y) @ v]
          = [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> Subst u u' (u \<ominus> y) @ Subst u u' y @ (z \<ominus> (u \<ominus> y) @ v)]"
            apply (subst append_assoc [THEN sym])
            apply (subst switch_par_comp_Subst, simp_all)
            apply (simp_all add: set_diff set_addvars distinct_diff)
            apply auto
            using  V  by (auto simp add: set_inter set_diff u_def y_def x_def v_def z_def) [1]

         have [simp]: "Subst (u @ (y \<oplus> (z \<ominus> v) \<ominus> u)) (u' @ (y \<oplus> (z \<ominus> v) \<ominus> u)) ((u \<ominus> y \<oplus> (z \<ominus> v)) @ y @ (z \<ominus> v)) 
            = Subst u  u' ((u \<ominus> y \<oplus> (z \<ominus> v)) @ y @ (z \<ominus> v))"
          apply (subst Subst_cancel_left, simp_all)
          by (simp add: type_length)

         thm par_switch_eq_a

         have J: "[u \<ominus> (y \<oplus> (z \<ominus> v)) \<leadsto> u \<ominus> (y \<oplus> (z \<ominus> v))] \<parallel> [v \<ominus> z \<leadsto> v \<ominus> z] =  [(u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z) \<leadsto> (u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z)]"
          apply (subst par_switch, simp_all, safe)
          apply (simp add: distinct_diff)
          using \<open>type_ok B\<close> distinct_diff type_ok_def v_def apply blast
          apply (simp add: set_diff set_addvars set_inter, auto)
          using U by (auto simp add: set_inter set_diff u_def y_def v_def z_def) [1]

         have [simp]: "distinct v"
          using \<open>type_ok B\<close> type_ok_def v_def by blast

         have [simp]: "distinct (z \<ominus> v)"
          by (simp add: distinct_diff)

         have [simp]: "distinct (u \<ominus> y)"
          by (simp add: distinct_diff)

         have [simp]: "distinct (u \<ominus> (y \<oplus> (z \<ominus> v)))"
          by (simp add: distinct_diff)

          have [simp]: "length u' = length u"
            by (simp add: type_length)

         have [simp]: "set (Subst u u' (u \<ominus> y)) \<subseteq> set u' \<union> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
          by (rule set_SubstI, simp_all add: set_diff set_addvars, auto)

         have [simp]: "set (Subst u u' y) \<subseteq> set u' \<union> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
          by (rule set_SubstI, simp_all add: set_diff set_addvars, auto)

        have [simp]: "set (z \<ominus> (u \<ominus> y) @ v) \<subseteq> set u' \<union> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
          apply (simp add: set_diff set_addvars, auto)
          using  V  by (auto simp add: set_inter set_diff u_def y_def x_def v_def z_def) [1]

        have [simp]: "set (Subst u u' (u \<ominus> (y \<oplus> (z \<ominus> v)))) \<subseteq> set u' \<union> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
          by (rule set_SubstI, simp_all add: set_diff set_addvars, auto)
        
        have [simp]: "set (Subst u u' (z \<ominus> v)) \<subseteq> set u' \<union> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
          by (rule set_SubstI, simp_all add: set_diff set_addvars, auto)

         def v' \<equiv> "newvars (u' @ u @ x @ y @ z) (TVs v)"  

         have [simp]: "distinct v'"
          by (simp add: v'_def)

        have a: "set (u' @ u @ x @ y @ z) \<inter> set v' = {}"
          by (simp add: v'_def del: set_append)

        from this have [simp]: "set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<inter> set v' = {}"
          by (simp add: set_diff set_addvars, auto)
          

         from a have [simp]: "set u' \<inter> set v' = {}"
          by auto

         have [simp]: "TVs v' = TVs v"
          by (simp add: v'_def)

         have [simp]: "set (Subst u u' (u \<ominus> (y \<oplus> (z \<ominus> v)))) \<subseteq> set u' \<union> (set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<union> set v')"
          by (rule set_SubstI, simp_all add: set_diff set_addvars, auto)

          have [simp]: " set v' \<subseteq> set u' \<union> (set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<union> set v')"
            by auto

         have [simp]: "set (Subst u u' (z \<ominus> v)) \<subseteq> set u' \<union> (set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<union> set v')"
          by (rule set_SubstI, simp_all add: set_diff set_addvars, auto)

          thm Subst_Subst_a
          thm Subst_Subst
         have [simp]: "length v' = length v"
          by (simp add: type_length)

         have [simp]: "set v \<inter> set (u \<ominus> (y \<oplus> (z \<ominus> v))) = {}"
          using U by (auto simp add: set_inter set_diff set_addvars u_def y_def x_def v_def z_def) [1]

        thm Subst_not_in

        thm Subst_Subst

      have "set (u \<ominus> y) \<subseteq> set (u \<ominus> v)"
        using U by (auto simp add: set_inter set_diff set_addvars u_def y_def x_def v_def z_def) [1]
            

       have Ka:"Subst ((u \<ominus> y) @ v) (Subst u u' (u \<ominus> y) @ v') z = Subst ((u \<ominus> y \<ominus> v) @ v) (Subst u u' (u \<ominus> y \<ominus> v) @ v') z"
        apply (subgoal_tac "(u \<ominus> y \<ominus> v) = (u \<ominus> y)")
        apply simp
        apply (rule diff_disjoint)
        using U by (auto simp add: set_inter set_diff set_addvars u_def y_def x_def v_def z_def) [1]

      thm Subst_cons

      thm Subst_Subst

      from a have [simp]: "set v' \<inter> set (z \<ominus> v) = {}"
        by (simp add: set_diff set_addvars, auto)


      from a have [simp]: " set v' \<inter> set (u \<ominus> y \<ominus> v) = {}"
       by  (simp add: set_diff set_addvars, auto)

       thm u'_def

      have [simp]: "set (Subst u u' (z \<ominus> v)) \<inter> set v = {}"
        apply (subgoal_tac "set (Subst u u' (z \<ominus> v)) \<subseteq> - set v")
        apply auto [1]
        apply (rule set_SubstI, simp_all add: set_diff)
        using b by auto
 
      have [simp]: "set (Subst u u' (u \<ominus> y \<ominus> v)) \<inter> set v = {}"
        apply (subgoal_tac "set (Subst u u' (u \<ominus> y \<ominus> v)) \<subseteq> - set v")
        apply auto [1]
        apply (rule set_SubstI, simp_all add: set_diff)
        using b by auto

      have [simp]: "set u \<inter> set y \<inter> set z = {}"
        using V by (auto simp add: set_inter set_diff set_addvars u_def y_def x_def v_def z_def) [1]
  
      have Kb: "Subst (v @ (z \<ominus> v)) (v' @ Subst u u' (z \<ominus> v)) z = Subst (v @ (u \<ominus> y \<ominus> v)) (v' @ Subst u u' (u \<ominus> y \<ominus> v)) z"
        apply (subst Subst_switch, simp_all)
        apply (simp add: set_diff)
        apply (subst Subst_comp, simp_all)
        apply (simp add: set_diff)
        apply auto [1]
        apply (subst Comp_assoc_new_subst_aux [of _ y], simp_all)

        apply (subst Subst_switch, simp_all)
        apply (simp add: set_diff)
        apply (subst Subst_comp, simp_all)
        by (auto simp add: set_diff) [1]

         have K: "Subst ((u \<ominus> y) @ v @ (z \<ominus> (u \<ominus> y) @ v)) (Subst u u' (u \<ominus> y) @ v' @ (z \<ominus> (u \<ominus> y) @ v)) ((u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z) @ z)
            = Subst u u' (u \<ominus> (y \<oplus> (z \<ominus> v))) @ Subst (v @ (z \<ominus> v)) (v' @ Subst u u' (z \<ominus> v)) ((v \<ominus> z) @ z)"
            apply (simp add: Subst_append, safe)
            apply (unfold append_assoc [THEN sym])
            apply (subst Subst_cancel_left)
            apply (auto simp add: set_diff) [2]
            apply (subst Subst_not_in, simp_all)
            apply (subst Subst_Subst, simp_all)
            apply (simp add: set_diff set_addvars, auto)

            apply (unfold append_assoc [THEN sym])
            apply (subst Subst_not_in, simp_all)
            apply (simp add: set_diff, auto)

            apply (subst (2) Subst_not_in, simp_all)
            apply (simp add: set_diff, auto)
            apply (subst Subst_not_in_a, simp_all)
            apply (simp add: set_diff, auto)
            using U apply (auto simp add: set_inter set_diff set_addvars u_def y_def x_def v_def z_def) [1]


            apply (unfold append_assoc [THEN sym])
            apply (subst Subst_cancel_left)
            apply (auto simp add: set_diff) [2]
            apply (simp add: Ka Kb)
            apply (subst Subst_switch, simp_all)
            by (simp add: set_diff, auto)
 
         thm Subst_Subst

         have I: "[u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> Subst u u' (u \<ominus> y) @ Subst u u' y @ (z \<ominus> (u \<ominus> y) @ v)] oo [u \<ominus> y \<leadsto> u \<ominus> y] \<parallel> Trs B \<parallel> [z \<ominus> (u \<ominus> y) @ v \<leadsto> z \<ominus> (u \<ominus> y) @ v] oo
            [(u \<ominus> y) @ v @ (z \<ominus> (u \<ominus> y) @ v) \<leadsto> (u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z) @ z]
             =
            [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> Subst u u' (u \<ominus> (y \<oplus> (z \<ominus> v))) @ Subst u u' y @ Subst u u' (z \<ominus> v)] oo [u \<ominus> (y \<oplus> (z \<ominus> v)) \<leadsto> u \<ominus> (y \<oplus> (z \<ominus> v))] \<parallel> Trs B \<parallel> [z \<ominus> v \<leadsto> z \<ominus> v] oo
            [u \<ominus> (y \<oplus> (z \<ominus> v)) \<leadsto> u \<ominus> (y \<oplus> (z \<ominus> v))] \<parallel> [v @ (z \<ominus> v) \<leadsto> (v \<ominus> z) @ z]"
          apply (rule_tac v = v' in par_switch_eq_a, simp_all add:  )
          apply (subst switch_comp_subst, simp_all)
          apply (simp add: set_diff)
          using U  apply (simp add: v_def u_def z_def y_def set_diff set_inter set_addvars)
          apply auto [1]
          apply safe         
          apply (meson UnE \<open>set (Subst u u' (u \<ominus> y)) \<subseteq> set u' \<union> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))\<close> subsetCE)
          using \<open>set (z \<ominus> (u \<ominus> y) @ v) \<subseteq> set (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))\<close> apply blast
          using U V apply (simp add: v_def u_def z_def y_def set_diff set_inter set_addvars)
          using U V apply (simp add: v_def u_def z_def y_def set_diff set_inter set_addvars)
          using U V apply (simp add: v_def u_def z_def y_def set_diff set_inter set_addvars)
          apply (subst switch_par_comp_Subst)
          apply (simp_all add: set_diff)
          by (simp add: K)

         have "?Ty = ?Tb"
            apply (simp add: diff_inter_left diff_inter_right H)
            apply (rule par_switch_eq, simp_all add:  )
            apply (simp add: comp_assoc [THEN sym]  )
            apply (simp add: Ha Hb Hc)
            apply (subst switch_comp_subst, simp_all)         
            apply (simp add: le_supI2)
            apply (metis \<open>set (u \<ominus> (u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))) \<subseteq> set u \<union> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))\<close> \<open>set (y \<oplus> (z \<ominus> v \<otimes> z)) \<subseteq> set u \<union> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))\<close> \<open>set (z \<ominus> v \<otimes> z) \<subseteq> set (y \<oplus> (z \<ominus> v \<otimes> z))\<close> \<open>set y \<subseteq> set (y \<oplus> (z \<ominus> v \<otimes> z))\<close> diff_inter_left diff_inter_right subset_trans)
            apply (simp add: Subst_append)
            using I apply (simp add: comp_assoc  )
            apply (subst J)

            by (simp add: J)


         from this E and F have " [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (x \<oplus> (y \<ominus> u \<otimes> y)) @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)] oo
              ([x \<oplus> (y \<ominus> u \<otimes> y) \<leadsto> x @ (y \<ominus> u \<otimes> y)] oo Trs A \<parallel> [y \<ominus> u \<otimes> y \<leadsto> y \<ominus> u \<otimes> y] oo [u @ (y \<ominus> u \<otimes> y) \<leadsto> (u \<ominus> u \<otimes> y) @ y] oo [u \<ominus> u \<otimes> y \<leadsto> u \<ominus> u \<otimes> y] \<parallel> Trs B) \<parallel>
              [z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z \<leadsto> z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z] oo
              [(u \<ominus> u \<otimes> y) @ v @ (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) @ z] oo
              [(u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (v \<ominus> v \<otimes> z)] \<parallel> Trs C 
              =
              [x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> x @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] oo
              [u @ (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<leadsto> (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) @ (y \<oplus> (z \<ominus> v \<otimes> z))] oo
              [u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)) \<leadsto> u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))] \<parallel>
              ([y \<oplus> (z \<ominus> v \<otimes> z) \<leadsto> y @ (z \<ominus> v \<otimes> z)] oo Trs B \<parallel> [z \<ominus> v \<otimes> z \<leadsto> z \<ominus> v \<otimes> z] oo [v @ (z \<ominus> v \<otimes> z) \<leadsto> (v \<ominus> v \<otimes> z) @ z] oo [v \<ominus> v \<otimes> z \<leadsto> v \<ominus> v \<otimes> z] \<parallel> Trs C)"
          by simp


          from this have C: "[In A \<oplus> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) \<leadsto> (In A \<oplus> (In B \<ominus> Out A \<otimes> In B)) @ (In C \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C)] oo
              ([In A \<oplus> (In B \<ominus> Out A \<otimes> In B) \<leadsto> In A @ (In B \<ominus> Out A \<otimes> In B)] oo Trs A \<parallel> [In B \<ominus> Out A \<otimes> In B \<leadsto> In B \<ominus> Out A \<otimes> In B] oo [Out A @ (In B \<ominus> Out A \<otimes> In B) \<leadsto> (Out A \<ominus> Out A \<otimes> In B) @ In B] oo
               [Out A \<ominus> Out A \<otimes> In B \<leadsto> Out A \<ominus> Out A \<otimes> In B] \<parallel> Trs B) \<parallel>
              [In C \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C \<leadsto> In C \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C] oo
              [(Out A \<ominus> Out A \<otimes> In B) @ Out B @ (In C \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C) \<leadsto> (Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) @ (Out B \<ominus> Out B \<otimes> In C) @ In C] oo
              [(Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) @ (Out B \<ominus> Out B \<otimes> In C) \<leadsto> (Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) @ (Out B \<ominus> Out B \<otimes> In C)] \<parallel> Trs C =
              [In A \<oplus> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) \<leadsto> In A @ (In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C)))] oo
              Trs A \<parallel> [In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C)) \<leadsto> In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))] oo
              [Out A @ (In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) \<leadsto> (Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))) @ (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))] oo
              [Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C)) \<leadsto> Out A \<ominus> Out A \<otimes> (In B \<oplus> (In C \<ominus> Out B \<otimes> In C))] \<parallel>
              ([In B \<oplus> (In C \<ominus> Out B \<otimes> In C) \<leadsto> In B @ (In C \<ominus> Out B \<otimes> In C)] oo Trs B \<parallel> [In C \<ominus> Out B \<otimes> In C \<leadsto> In C \<ominus> Out B \<otimes> In C] oo [Out B @ (In C \<ominus> Out B \<otimes> In C) \<leadsto> (Out B \<ominus> Out B \<otimes> In C) @ In C] oo
               [Out B \<ominus> Out B \<otimes> In C \<leadsto> Out B \<ominus> Out B \<otimes> In C] \<parallel> Trs C)"
             by (simp add: x_def [THEN symmetric] y_def [THEN symmetric] z_def [THEN symmetric] u_def [THEN symmetric] v_def [THEN symmetric] w_def [THEN symmetric])

          show "A ;; B ;; C = A ;; (B ;; C)"
            by (simp add: Comp_def Let_def Var_def A B C)
      qed
         


      lemma Comp_assoc: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow>
          set (In A) \<inter> set (In B) = {} \<Longrightarrow> set (In B) \<inter> set (In C) = {} \<Longrightarrow> set (In A) \<inter> set (In C) = {} \<Longrightarrow>
          set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> set (Out B) \<inter> set (Out C) = {} \<Longrightarrow> set (Out A) \<inter> set (Out C) = {} \<Longrightarrow>
          A ;; B ;; C = A ;; (B ;; C)"
        proof - 
          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"
          assume [simp]: "type_ok C"
          assume [simp]: "set (In A) \<inter> set (In B) = {}"
          assume [simp]: "set (Out A) \<inter> set (Out B) = {}"
          assume [simp]: "set (In B) \<inter> set (In C) = {}"
          assume [simp]: "set (Out B) \<inter> set (Out C) = {}"
          assume [simp]: "set (In A) \<inter> set (In C) = {}"
          assume [simp]: "set (Out A) \<inter> set (Out C) = {}"
          
          def IA' \<equiv> "In A"
          def IB' \<equiv> "In B \<ominus> Out A"
          def IC' \<equiv> "In C \<ominus> Out B \<ominus> Out A"

          def OA' \<equiv> "Out A \<ominus> In C \<ominus> In B"
          def OB' \<equiv> "Out B \<ominus> In C"
          def OC' \<equiv> "Out C"

          def I' \<equiv> "IA' @ IB' @ IC'"
          def O' \<equiv> "OA' @ OB' @ OC'"

          def ICA \<equiv> "Out A \<otimes> In C"
          def ICB \<equiv> "In C \<ominus> Var B C"
          def OAB \<equiv> "Out A \<ominus> Var A B"

          have [simp]: "In C \<ominus> ((Out A \<ominus> In B) @ Out B) = IC'"
            by (simp add: IC'_def Int_commute diff_notin diff_sym diff_union)

          have [simp]: "(In B @ (In C \<ominus> Out B)) \<ominus> Out A = IB' @ IC'"
            by (simp add: IB'_def IC'_def union_diff)

          have [simp]: "Out A \<ominus> (In B @ (In C \<ominus> Out B)) = OA'"
            by (simp add: OA'_def diff_cancel_set diff_sym diff_union)

          have [simp]: "In A @ (In B \<ominus> Out A \<otimes> In B) @ (In C \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C) = I'"
            by (simp add: I'_def IA'_def diff_inter_right IB'_def diff_inter_left)

          have [simp]: "perm (Out A \<otimes> (In B @ (In C \<ominus> Out B))) ((Out A \<otimes> In B) @ (Out A \<otimes> In C))"
            apply (cut_tac x= "Out A" and y = "In B" and z= "In C \<ominus> Out B" in  inter_append)
            apply (subgoal_tac "set (In B) \<inter> set (In C) = {}")
            apply (metis empty_inter_diff set_empty set_inter)
            by (simp_all add: inter_diff_empty)

          have [simp]: "((Out A \<ominus> Out A \<otimes> In B) @ Out B \<ominus> (Out A \<ominus> Out A \<otimes> In B) @ Out B \<otimes> In C) @ Out C = O'"
            by (simp add: O'_def OC'_def diff_inter_left diff_inter_right union_diff OB'_def OA'_def diff_sym)

          have A_in_tp: "TI (Trs A) = TVs (In A)"
            by (metis \<open>type_ok A\<close> type_ok_def)

          have A_out_tp: "TO (Trs A) = TVs (Out A)"
            by (metis \<open>type_ok A\<close> type_ok_def)

          have B_in_tp: "TI (Trs B) = TVs (In B)"
            by (metis \<open>type_ok B\<close> type_ok_def)

          have B_out_tp: "TO (Trs B) = TVs (Out B)"
            by (metis \<open>type_ok B\<close> type_ok_def)

          have C_in_tp: "TI (Trs C) = TVs (In C)"
            by (metis \<open>type_ok C\<close> type_ok_def)

          have C_out_tp: "TO (Trs C) = TVs (Out C)"
            by (metis \<open>type_ok C\<close> type_ok_def)

          have [simp]: "TVs (In A) @ TVs (In B \<ominus> Var A B) = TI (Trs A \<parallel> [In B \<ominus> Var A B \<leadsto> In B \<ominus> Var A B] oo [Out A @ (In B \<ominus> Var A B) \<leadsto> (Out A \<ominus> Var A B) @ In B] oo [Out A \<ominus> Var A B \<leadsto> Out A \<ominus> Var A B] \<parallel> Trs B)"
            apply (subst TI_comp)
            apply (simp )
            apply (subst TO_comp)
            apply (simp add:  A_out_tp)
            apply (simp add:  B_in_tp)
            apply (subst TI_comp)
            apply (simp add:  A_out_tp)
            by (simp add:  A_in_tp)

          have [simp]: "TVs (Out A \<ominus> Var A B) @ TVs (Out B) = TO (Trs A \<parallel> [In B \<ominus> Var A B \<leadsto> In B \<ominus> Var A B] oo [Out A @ (In B \<ominus> Var A B) \<leadsto> (Out A \<ominus> Var A B) @ In B] oo [Out A \<ominus> Var A B \<leadsto> Out A \<ominus> Var A B] \<parallel> Trs B)"
            apply (subst TO_comp)
            apply (simp)
            apply (subst TO_comp)
            by (simp_all add:   A_out_tp B_in_tp B_out_tp)

          have [simp]: "distinct (In A)"
            using \<open>type_ok A\<close> type_ok_def by blast

          have [simp]: "distinct (In B \<ominus> Var A B)"
            using \<open>type_ok B\<close> distinct_diff type_ok_def by blast

          have [simp]: "set (In A) \<inter> set (In B \<ominus> Var A B) = {}"
            by (metis \<open>set (In A) \<inter> set (In B) = {}\<close> empty_inter_diff set_empty set_inter)

          have [simp]: "distinct (Out A \<ominus> Var A B)"
            using \<open>type_ok A\<close> distinct_diff type_ok_def by blast
          
          have [simp]: "distinct (Out B)"
            using \<open>type_ok B\<close> type_ok_def by blast

          have [simp]: "set (Out A \<ominus> Var A B) \<inter> set (Out B) = {}"
            by (metis Int_commute \<open>set (Out A) \<inter> set (Out B) = {}\<close> empty_inter_diff empty_set set_inter)

          have [simp]: "(set (In A) \<union> set (In B \<ominus> Var A B)) \<inter> set (In C) = {}"
            apply (simp add: Int_Un_distrib2)
            by (metis \<open>set (In B) \<inter> set (In C) = {}\<close> disjoint_iff_not_equal inter_subset notin_inter)

          have [simp]: "(set (Out A \<ominus> Var A B) \<union> set (Out B)) \<inter> set (Out C) = {}"
            apply (simp add: Int_Un_distrib2)
            by (metis \<open>set (Out A) \<inter> set (Out C) = {}\<close> disjoint_iff_not_equal inter_subset notin_inter)

          have [simp]: "distinct IC'"
            apply (simp add: IC'_def)
            using \<open>type_ok C\<close> distinct_diff type_ok_def by blast

          have [simp]: "distinct IB'"
            apply (simp add: IB'_def)
            using \<open>type_ok B\<close> distinct_diff type_ok_def by blast

          have [simp]: "TO (Trs A \<parallel> [IB' \<leadsto> IB'] oo [Out A @ IB' \<leadsto> (Out A \<ominus> Var A B) @ In B]) = TVs (Out A \<ominus> Var A B) @ TI (Trs B)"
            by (simp add:   A_out_tp B_in_tp)

          have [simp]: "distinct (Out A)"
            using \<open>type_ok A\<close> type_ok_def by blast

          have [simp]: "distinct (In B \<ominus> Out A)"
            using \<open>type_ok B\<close> distinct_diff type_ok_def by blast

          have [simp]: "distinct (In C \<ominus> Out B \<ominus> Out A)"
            using IC'_def \<open>distinct IC'\<close> by blast

          have [simp]: "set (In B \<ominus> Out A) \<inter> set (In C \<ominus> Out B \<ominus> Out A) = {}"
            apply (simp add: set_diff)
            by (metis Diff_Int_distrib2 Diff_cancel Int_Diff \<open>set (In B) \<inter> set (In C) = {}\<close>)

          have [simp]: "set (Out A) \<inter> set (In B \<ominus> Out A) = {}"
            by (simp add: set_diff)
            
          have [simp]: "set (Out A) \<inter> set (In C \<ominus> Out B \<ominus> Out A) = {}"
            by (simp add: set_diff)
          
          have A: "set ((Out A \<ominus> Var A B) @ In B) \<subseteq> set (Out A @ IB')"
            apply (simp add: IB'_def Var_def diff_inter_right diff_inter_left)
            by (metis addvars_def inf_sup_aci(5) set_addvars set_append sup_ge2)

          have [simp]: "set IB' \<inter> set IC' = {}"
            by (simp add: IB'_def IC'_def)

          have [simp]: "TVs (In B) @ TVs (In C \<ominus> Var B C) = TI (Trs B \<parallel> [In C \<ominus> Var B C \<leadsto> In C \<ominus> Var B C] oo [Out B @ (In C \<ominus> Var B C) \<leadsto> (Out B \<ominus> Var B C) @ In C] oo [Out B \<ominus> Var B C \<leadsto> Out B \<ominus> Var B C] \<parallel> Trs C)"
            by (simp add:   B_in_tp B_out_tp C_in_tp)

          have [simp]: "TVs (Out B \<ominus> Var B C) @ TVs (Out C) = TO (Trs B \<parallel> [In C \<ominus> Var B C \<leadsto> In C \<ominus> Var B C] oo [Out B @ (In C \<ominus> Var B C) \<leadsto> (Out B \<ominus> Var B C) @ In C] oo [Out B \<ominus> Var B C \<leadsto> Out B \<ominus> Var B C] \<parallel> Trs C)"
            by (simp add:   B_out_tp C_in_tp C_out_tp)

          have [simp]: "distinct (In B)"
            using \<open>type_ok B\<close> type_ok_def by blast

          have [simp]: "distinct (In C \<ominus> Var B C)"
            using \<open>type_ok C\<close> distinct_diff type_ok_def by blast

          have [simp]: "set (In B) \<inter> set (In C \<ominus> Var B C) = {}"
            by (metis \<open>set (In B) \<inter> set (In C) = {}\<close> empty_inter_diff set_empty set_inter)

          have [simp]: "distinct (Out B \<ominus> Var B C)"
            by (simp add: distinct_diff)

          have [simp]: "distinct (Out C)"
            using \<open>type_ok C\<close> type_ok_def by blast

          have [simp]: "set (Out B \<ominus> Var B C) \<inter> set (Out C) = {}"
            by (metis \<open>set (Out B) \<inter> set (Out C) = {}\<close> disjoint_iff_not_equal inter_subset notin_inter)

          have [simp]: "set (In A) \<inter> set (In C \<ominus> Var B C) = {}"
            by (metis \<open>set (In A) \<inter> set (In C) = {}\<close> empty_inter_diff empty_set set_inter)

          have [simp]: "set (Out A) \<inter> set (Out B \<ominus> Var B C) = {}"
            by (metis \<open>set (Out A) \<inter> set (Out B) = {}\<close> empty_inter_diff empty_set set_inter)

          have [simp]: "In B @ (In C \<ominus> Out B \<otimes> In C) \<ominus> Out A \<otimes> In B @ (In C \<ominus> Out B \<otimes> In C) = IB' @ IC'"
            by (simp add: diff_inter_right)

          have [simp]: "In A @ IB' @ IC' = I'"
            by (simp add: I'_def IA'_def)

          have [simp]: "(Out A \<ominus> Out A \<otimes> In B @ (In C \<ominus> Out B \<otimes> In C)) = OA'"
            by (simp add: diff_inter_right diff_inter_left)

          have [simp]: "OA' @ (Out B \<ominus> Out B \<otimes> In C) @ Out C = O'"
            by (simp add: O'_def OC'_def diff_inter_right diff_inter_left OB'_def)

          have [simp]: "distinct OA'"
            by (simp add: OA'_def distinct_diff)

          have [simp]: "TO (Trs B \<parallel> [In C \<ominus> Var B C \<leadsto> In C \<ominus> Var B C] oo [Out B @ (In C \<ominus> Var B C) \<leadsto> OB' @ In C]) = TI ([OB' \<leadsto> OB'] \<parallel> Trs C)"
            by (simp add:   B_out_tp C_in_tp)

          have [simp]: "set (Out B) \<inter> set (In C \<ominus> Var B C) = {}"
            by (simp add: Var_def diff_inter_right set_diff)

          have [simp]: "set OA' \<inter> set (Out B) = {}"
            apply (simp add: OA'_def)
            by (metis \<open>set (Out A) \<inter> set (Out B) = {}\<close> empty_inter_diff inf.commute set_empty set_inter)

          have [simp]: "set OA' \<inter> set (In C \<ominus> Var B C) = {}"
            apply (simp add: OA'_def Var_def diff_inter_right)
            by (metis (no_types, lifting) DiffE disjoint_iff_not_equal set_diff)

          have [simp]: "set OB' \<subseteq> set (Out B) \<union> set (In C \<ominus> Var B C)"
            apply (simp add: OB'_def Var_def diff_inter_right)
            using set_diff by fastforce

          have [simp]: "set (In C) \<subseteq> set (Out B) \<union> set (In C \<ominus> Var B C)"
            by (simp add: Var_def diff_inter_right set_diff)

          have [simp]: "distinct OB'"
            by (simp add: OB'_def distinct_diff)

          have [simp]: "set OA' \<inter> set OB' = {}"
            apply (simp add: OB'_def)
            by (metis \<open>set OA' \<inter> set (Out B) = {}\<close> empty_inter_diff empty_set set_inter)

          have [simp]: "distinct OAB"
            by (simp add: OAB_def)

          have [simp]: "perm OAB (OA' @ ICA)"
            apply (simp add: OAB_def OA'_def ICA_def Var_def diff_inter_left diff_sym)
            apply (subgoal_tac "Out A \<otimes> In C = (Out A \<ominus> In B) \<otimes> In C")
            apply (simp add: perm_diff_right_inter)
            by (simp add: diff_emptyset empty_inter inter_diff_distrib)

          have [simp]:"set (In B) \<inter> set IC' = {}"
            apply (simp add: IC'_def)
            by (metis \<open>set (In B) \<inter> set (In C) = {}\<close> empty_inter_diff empty_set set_inter)

          have aa: "ID (TI (Trs B \<parallel> [IC' \<leadsto> IC'])) = [In B @ IC' \<leadsto> In B @ IC']"
            apply (cut_tac x= "In B @ IC'" in distinct_id)
            apply simp
            apply (subgoal_tac "TVs (In B @ IC') = TI (Trs B \<parallel> [IC' \<leadsto> IC'])")
            by (simp_all add: B_in_tp)

          have [simp]: "set (Out B) \<inter> set IC' = {}"
            apply (simp add: IC'_def set_diff)
            by blast
            
          have bb: "ID (TO (Trs B \<parallel> [IC' \<leadsto> IC'])) = [Out B @ IC' \<leadsto> Out B @ IC']"
            apply (cut_tac x = "Out B @ IC'" in distinct_id)
            apply simp
            apply (subgoal_tac "TVs (Out B @ IC') = TO (Trs B \<parallel> [IC' \<leadsto> IC'])")
            by (simp_all add: B_out_tp)

          have [simp]: "set OA' \<inter> set (In B) = {}"
            apply (simp add: OA'_def set_diff)
            by blast

          have cc: "ID (TI ([OA' \<leadsto> OA'] \<parallel> Trs B)) = [OA' @ In B \<leadsto> OA'@ In B]"
            apply (cut_tac x="OA' @ In B" in distinct_id)
            apply simp
            apply (subgoal_tac "TVs (OA' @ In B) = TI ([OA' \<leadsto> OA'] \<parallel> Trs B)")
            by (simp_all add: B_in_tp)

          have dd: "ID (TO ([OA' \<leadsto> OA'] \<parallel> Trs B)) = [OA' @ Out B \<leadsto> OA' @ Out B]"
            apply (cut_tac x="OA' @ Out B" in distinct_id)
            apply simp
            apply (subgoal_tac "TVs (OA' @ Out B) = TO ([OA' \<leadsto> OA'] \<parallel> Trs B)")
            by (simp_all add: B_out_tp)

          have [simp]: "set OAB \<inter> set (In B) = {}"
            apply (simp add: OAB_def Var_def diff_inter_left set_diff)
            by blast
            
          have [simp]: "set OAB \<inter> set IC' = {}"
            apply (simp add: OAB_def IC'_def Var_def diff_inter_left set_diff)
            by blast

          have [simp]: "set OA' \<subseteq> set OAB"
            apply (simp add: OAB_def Var_def diff_inter_left OA'_def set_diff)
            by blast

          have [simp]: "set ICA \<subseteq> set OAB"
            apply (simp add: OAB_def Var_def diff_inter_left ICA_def)
            by (metis diff_emptyset \<open>set (In B) \<inter> set (In C) = {}\<close> empty_inter_diff inter_diff_distrib notin_inter subsetI)

          have [simp]: "distinct ICA"
            by (simp add: ICA_def distinct_inter)

          have [simp]: "set ICA \<inter> set (Out B) = {}"
            apply (simp add: ICA_def set_inter)
            apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
            apply blast
            by simp

          have [simp]: "set ICA \<inter> set IC' = {}"
            apply (simp add: ICA_def IC'_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set ICA = {}"
            apply (simp add: OA'_def ICA_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set IC' = {}"
            apply (simp add: OA'_def IC'_def set_diff)
            by blast

          have [simp]: "set OAB \<subseteq> set OA' \<union> set ICA"
            apply (simp add: OAB_def OA'_def ICA_def Var_def diff_inter_left diff_sym)
            apply (subgoal_tac "Out A \<otimes> In C = (Out A \<ominus> In B) \<otimes> In C")
            apply simp
            apply (simp add: set_diff set_inter)
            apply blast
            by (metis diff_emptyset \<open>set (In B) \<inter> set (In C) = {}\<close> inter_diff_distrib set_empty set_inter)

          have [simp]: "set (Out A) \<inter> set IB' = {}"
            by (simp add: IB'_def)

          have [simp]: "set (Out A) \<inter> set IC' = {}"
            by (simp add: IC'_def)

          have [simp]: "perm (Out A @ IB') (OAB @ In B)"
            by (simp add: IB'_def OAB_def Var_def diff_inter_left perm_switch)

          have [simp]: "perm (Out A @ IB' @ IC') (OAB @ In B @ IC')"
            using \<open>perm (Out A @ IB') (OAB @ In B)\<close> perm_union_left by fastforce

          have [simp]: "perm (OA' @ ICA @ Out B @ IC') (OAB @ Out B @ IC')"
            by (metis \<open>perm OAB (OA' @ ICA)\<close> append_assoc perm_def perm_union_left)

          have [simp]: "perm (Out A @ IB' @ IC') (OA' @ ICA @ In B @ IC')"
            by (metis \<open>perm (Out A @ IB' @ IC') (OAB @ In B @ IC')\<close> \<open>perm OAB (OA' @ ICA)\<close> append_assoc mset_append perm_def)

          have [simp]: "set ICA \<inter> set (In B) = {}"
            apply (simp add: ICA_def set_inter)
            by (metis Int_commute \<open>set (In B) \<inter> set (In C) = {}\<close> inf_bot_right inf_left_commute)

          have [simp]: "set (Out B) \<inter> set ICA = {}"
            by (metis \<open>set ICA \<inter> set (Out B) = {}\<close> inf_commute set_inter)

          have [simp]: "TO ([ICA @ In B \<leadsto> In B @ ICA] oo Trs B \<parallel> [ICA \<leadsto> ICA]) = TVs (Out B) @ TVs ICA"
            by (simp add:  B_in_tp B_out_tp)

          have [simp]: "TO ([OA' \<leadsto> OA'] \<parallel> [ICA @ In B \<leadsto> In B @ ICA] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA]) = TVs OA' @ TVs (Out B) @ TVs ICA"
            by (simp add:   B_in_tp B_out_tp)

          have [simp]: "perm (ICA @ IC') ICB"
            apply (simp add: ICA_def IC'_def ICB_def Var_def diff_inter_right)
            by (metis (no_types, hide_lams) Var_def \<open>distinct (In C \<ominus> Var B C)\<close> \<open>distinct (Out A)\<close> \<open>set (Out A) \<inter> set (Out B) = {}\<close> diff_inter_right perm_switch_aux_f inter_diff_empty)            

          have [simp]: "set (In B) \<inter> set ICA = {}"
            apply (simp add: ICA_def set_inter)
            using \<open>set (In B) \<inter> set (In C) = {}\<close> by blast

          have [simp]: "set ICB \<subseteq> set ICA \<union> set IC'"
            apply (simp add: ICB_def ICA_def IC'_def Var_def diff_inter_right set_diff set_inter)
            by blast

          have [simp]: "distinct ICB"
            by (simp add: ICB_def)

          have [simp]: "set (Out B) \<inter> set ICB = {}"
            by (simp add: ICB_def)

          have [simp]: "set OA' \<inter> set ICB = {}"
            by (simp add: ICB_def)

          have [simp]: "set ICA \<subseteq> set ICB"
            apply (simp add: ICB_def Var_def diff_inter_right set_diff)
            using ICA_def \<open>set ICA \<inter> set (Out B) = {}\<close> set_inter by fastforce

          have [simp]: "set IC' \<subseteq> set ICB"
            apply (simp add: IC'_def ICB_def Var_def diff_inter_right set_diff)
            by blast

          have [simp]: "perm (Out A @ IB' @ IC') (OA' @ In B @ ICA @ IC')"
            by (metis (no_types, hide_lams) \<open>perm (Out A @ IB' @ IC') (OA' @ ICA @ In B @ IC')\<close> append_assoc perm_tp perm_trans perm_union_right)

          have [simp]: "perm (OA' @ Out B @ ICB) (OA' @ Out B @ ICA @ IC')"
            by (metis \<open>perm (ICA @ IC') ICB\<close> perm_def perm_union_right)

          have trs_aux: "[OA' \<leadsto> OA'] \<parallel> (Trs B \<parallel> [ICB \<leadsto> ICB] oo [Out B @ ICB \<leadsto> OB' @ In C] oo [OB' \<leadsto> OB'] \<parallel> Trs C) = 
            [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo [OA' @ Out B @ ICB \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            apply (subst id_par_comp)
            apply (simp_all add: ICB_def)
            apply (simp add: par_assoc)
            apply (subst id_par_comp)
            apply (simp_all add: B_out_tp)
            apply (subst par_switch)  
            apply simp_all           
            apply (simp add: par_assoc[THEN sym])
            by (simp add: par_switch)

          have "A ;; (B ;; C) = 
            \<lparr>In = I', Out = O', Trs = Trs A \<parallel> [IB' @ IC'  \<leadsto> IB' @ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICB] oo [OA' \<leadsto> OA'] \<parallel> (Trs B \<parallel> [ICB \<leadsto> ICB] oo 
              [Out B @ ICB \<leadsto> OB' @ In C] oo [OB' \<leadsto> OB'] \<parallel> Trs C)  \<rparr>"
            (is "_ = \<lparr>In=I',Out=O',Trs = ?TBCA\<rparr>")
            apply (simp add: Comp_in_disjoint Let_def)
            apply (subst Comp_in_disjoint)
            apply simp
            apply (simp add: type_ok_def)
            apply simp_all
            apply (simp add: Let_def Var_def ICB_def)
            by (simp add: OB'_def diff_inter_left)

          have "A ;; B ;; C = 
            \<lparr>In = I', Out = O', Trs = (Trs A \<parallel> [IB' \<leadsto> IB'] oo [Out A @ IB' \<leadsto> OAB @ In B] oo [OAB \<leadsto> OAB] \<parallel> Trs B) \<parallel> [IC' \<leadsto> IC'] oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C  \<rparr>"
            (is "_ = \<lparr>In=I',Out=O',Trs = ?TABC\<rparr>")
            apply (simp add: Comp_in_disjoint Let_def)
            apply (subst Comp_in_disjoint)
            apply (simp add: type_ok_def)
            apply simp_all
            apply (simp add: Let_def Var_def OAB_def)
            apply (simp add: IB'_def IC'_def OA'_def OB'_def)
            by (simp add: diff_inter_left diff_inter_right union_diff  diff_sym IC'_def)

         
         have "?TABC = (Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [IC' \<leadsto> IC'] oo [Out A @ IB' \<leadsto> OAB @ In B] \<parallel> [IC' \<leadsto> IC'] oo [OAB \<leadsto> OAB] \<parallel> Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            apply (subst par_id_comp)
            apply (simp_all add: OAB_def)
            apply (subst par_id_comp)
            by (simp_all add: A_out_tp)
         also have "... = (Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo [OAB \<leadsto> OAB] \<parallel> Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            apply (subst par_switch)
            apply (simp add: IB'_def IC'_def)
            apply (simp only: A OAB_def)
            apply simp
            apply (subst par_assoc)
            by (simp add: par_switch)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo [OAB \<leadsto> OAB] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            by (simp add: par_assoc)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo ([OAB \<leadsto> OA' @ ICA] oo [OA' @ ICA \<leadsto> OA' @ ICA] oo [OA' @ ICA \<leadsto> OAB]) \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            by (simp add: switch_comp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo 
              (([OAB \<leadsto> OA' @ ICA] oo [OA' @ ICA \<leadsto> OA' @ ICA]) \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo [OA' @ ICA \<leadsto> OAB] \<parallel> ID (TO (Trs B \<parallel> [IC' \<leadsto> IC']))) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            apply (subst comp_parallel_distrib)
            apply (simp)
            apply (simp)
            by (simp only: comp_id_right)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo 
              ([OAB \<leadsto> OA' @ ICA] \<parallel> ID (TI (Trs B \<parallel> [IC' \<leadsto> IC'])) oo [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo [OA' @ ICA \<leadsto> OAB] \<parallel> ID (TO (Trs B \<parallel> [IC' \<leadsto> IC']))) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            apply (subst(2) comp_parallel_distrib)
            apply (simp add:  )
            apply (simp add: )
            by (simp only: comp_id_left)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo 
              ([OAB \<leadsto> OA' @ ICA] \<parallel> [In B @ IC' \<leadsto> In B @ IC'] oo [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo [OA' @ ICA \<leadsto> OAB] \<parallel> ID (TO (Trs B \<parallel> [IC' \<leadsto> IC']))) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            by (simp only: aa)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo 
              ([OAB \<leadsto> OA' @ ICA] \<parallel> [In B @ IC' \<leadsto> In B @ IC'] oo [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo [OA' @ ICA \<leadsto> OAB] \<parallel> [Out B @ IC' \<leadsto> Out B @ IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"         
            by (simp only: bb)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo 
              ([OAB @ In B @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo [OA' @ ICA \<leadsto> OAB] \<parallel> [Out B @ IC' \<leadsto> Out B @ IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"     
            by (simp add: par_switch)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo 
              ([OAB @ In B @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo [OA' @ ICA @ Out B @ IC' \<leadsto> OAB @ Out B @ IC']) oo 
              [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"    
            by (simp add: par_switch)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo 
              ([Out A @ IB' @ IC'  \<leadsto> OAB @ In B @ IC'] oo [OAB @ In B @ IC' \<leadsto> OA' @ ICA @ In B @ IC']) oo 
              [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              ([OA' @ ICA @ Out B @ IC' \<leadsto> OAB @ Out B @ IC'] oo [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C]) oo 
              [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           by (simp add: comp_assoc   A_out_tp B_in_tp B_out_tp C_in_tp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              ([OA' @ ICA @ Out B @ IC' \<leadsto> OAB @ Out B @ IC'] oo [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C]) oo 
              [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
            apply (subst switch_comp, simp_all)
            using \<open>set ICA \<subseteq> set OAB\<close> \<open>set OA' \<subseteq> set OAB\<close> by blast
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              [OA' @ ICA \<leadsto> OA' @ ICA] \<parallel> (Trs B \<parallel> [IC' \<leadsto> IC']) oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
            apply (subst switch_comp)
            apply (simp_all, safe)
            using \<open>set OA' \<subseteq> set OAB\<close> apply blast
            apply (metis OB'_def inter_subset notin_inter)
            apply (simp add: IC'_def set_diff OAB_def Var_def set_inter, auto)
            using \<open>set (In B) \<inter> set (In C) = {}\<close> by blast
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> [ICA \<leadsto> ICA] \<parallel> Trs B \<parallel> [IC' \<leadsto> IC'] oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
            by (simp add: par_switch par_assoc)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> ([ICA \<leadsto> ICA] \<parallel> Trs B) \<parallel> [IC' \<leadsto> IC'] oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
            by (simp add: par_assoc)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> 
                ([ICA @ In B \<leadsto> In B @ ICA] oo Trs B \<parallel> [ICA \<leadsto> ICA] oo [Out B @ ICA \<leadsto> ICA @ Out B]) \<parallel> 
                [IC' \<leadsto> IC'] oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
            apply (cut_tac S="[ICA \<leadsto> ICA]" and T = "Trs B" and x="ICA" and y="In B" and u="Out B" and v ="ICA" in switch_par)
            by (simp_all add: B_in_tp B_out_tp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              ([OA' \<leadsto> OA'] \<parallel> [ICA @ In B \<leadsto> In B @ ICA] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] oo  [OA' \<leadsto> OA'] \<parallel> [Out B @ ICA \<leadsto> ICA @ Out B]) \<parallel> 
                [IC' \<leadsto> IC'] oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           apply (subst id_par_comp)
           apply simp_all
           apply (subst id_par_comp)
           apply (simp_all add: B_in_tp)
           by (simp add: par_assoc)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              ([OA' \<leadsto> OA'] \<parallel> [ICA @ In B \<leadsto> In B @ ICA] \<parallel> [IC' \<leadsto> IC'] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC'] oo [OA' \<leadsto> OA'] \<parallel> [Out B @ ICA \<leadsto> ICA @ Out B] \<parallel> [IC' \<leadsto> IC']) oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           apply (subst par_id_comp)
           apply simp_all
           apply (subst par_id_comp)
           by (simp_all add: B_in_tp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              ([OA'@ ICA @ In B @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC'] oo [OA' \<leadsto> OA'] \<parallel> [Out B @ ICA \<leadsto> ICA @ Out B] \<parallel> [IC' \<leadsto> IC']) oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           apply (subst par_switch)
           apply simp_all
           apply (subst par_switch)
           apply simp_all
           by blast
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo 
              ([OA'@ ICA @ In B @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC'] oo [OA' @ Out B @ ICA @ IC'\<leadsto> OA' @  ICA @ Out B @ IC']) oo 
              [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           apply (subst par_switch)
           apply simp_all
           apply (subst par_switch)
           apply simp_all
           by blast
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo 
              ([Out A @ IB' @ IC' \<leadsto> OA' @ ICA @ In B @ IC'] oo [OA'@ ICA @ In B @ IC' \<leadsto> OA' @ In B @ ICA @ IC']) oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC'] oo 
              ([OA' @ Out B @ ICA @ IC'\<leadsto> OA' @  ICA @ Out B @ IC'] oo [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C]) oo 
              [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           by (simp add: comp_assoc   A_out_tp B_in_tp B_out_tp C_in_tp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC'] oo 
              ([OA' @ Out B @ ICA @ IC'\<leadsto> OA' @  ICA @ Out B @ IC'] oo [OA' @ ICA @ Out B @ IC' \<leadsto> OA' @ OB' @ In C]) oo 
              [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           by (subst switch_comp, auto)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC'] oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           apply (subst switch_comp)
           apply (simp_all)
           using perm_tp perm_union_left perm_union_right apply fastforce
           apply safe
           apply (metis OB'_def inter_subset notin_inter)
           by (simp add: IC'_def ICA_def set_diff set_inter)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> ([ICA \<leadsto> ICA] \<parallel> [IC' \<leadsto> IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           by (simp add: par_assoc)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICA @ IC' \<leadsto> ICA @ IC'] oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           by (simp add: par_switch)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> 
                ([ICA @ IC' \<leadsto> ICB] oo [ICB \<leadsto> ICB] oo [ICB \<leadsto> ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"  
           by (simp add: switch_comp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              ([OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> ([ICA @ IC' \<leadsto> ICB] oo [ICB \<leadsto> ICB]) oo ID (TO ([OA' \<leadsto> OA'] \<parallel> Trs B)) \<parallel> [ICB \<leadsto> ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           apply (subst comp_parallel_distrib)
           apply simp
           apply (simp )
           by (simp only: comp_id_right)           
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              (ID (TI ([OA' \<leadsto> OA'] \<parallel> Trs B)) \<parallel> [ICA @ IC' \<leadsto> ICB] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo ID (TO ([OA' \<leadsto> OA'] \<parallel> Trs B)) \<parallel> [ICB \<leadsto> ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           apply (subst(2) comp_parallel_distrib)
           apply simp
           apply (simp )
           by (simp only: comp_id_left)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              ([OA' @ In B  \<leadsto> OA' @ In B] \<parallel> [ICA @ IC' \<leadsto> ICB] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo ID (TO ([OA' \<leadsto> OA'] \<parallel> Trs B)) \<parallel> [ICB \<leadsto> ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           by (simp only: cc)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              ([OA' @ In B  \<leadsto> OA' @ In B] \<parallel> [ICA @ IC' \<leadsto> ICB] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo [OA' @ Out B \<leadsto> OA' @ Out B] \<parallel> [ICB \<leadsto> ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           by (simp only: dd)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              ([OA' @ In B @ ICA @ IC' \<leadsto> OA' @ In B @ ICB] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo [OA' @ Out B \<leadsto> OA' @ Out B] \<parallel> [ICB \<leadsto> ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           by (simp add: par_switch)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo 
              ([OA' @ In B @ ICA @ IC' \<leadsto> OA' @ In B @ ICB] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo [OA' @ Out B @ ICB \<leadsto> OA' @ Out B @ ICA @ IC']) oo 
              [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           by (simp add: par_switch)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  
              ([Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICA @ IC'] oo [OA' @ In B @ ICA @ IC' \<leadsto> OA' @ In B @ ICB]) oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo 
              ([OA' @ Out B @ ICB \<leadsto> OA' @ Out B @ ICA @ IC'] oo [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C])
              oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           by (simp add: comp_assoc   A_out_tp B_in_tp B_out_tp C_in_tp)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICB] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo 
              ([OA' @ Out B @ ICB \<leadsto> OA' @ Out B @ ICA @ IC'] oo [OA' @ Out B @ ICA @ IC' \<leadsto> OA' @ OB' @ In C])
              oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           apply (subst switch_comp, simp_all)
           apply safe
           by (meson Un_iff \<open>set ICB \<subseteq> set ICA \<union> set IC'\<close> rev_subsetD)
         also have "... = Trs A \<parallel> [IB' @ IC' \<leadsto> IB'@ IC'] oo  [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICB] oo 
              [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo 
              [OA' @ Out B @ ICB \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C"
           apply (subst switch_comp, simp_all)
           apply safe
           apply (simp add: OB'_def set_diff)
           by (simp add: IC'_def ICA_def set_diff set_inter)
         also have "... = ?TBCA"
          apply (simp add: trs_aux)
          by (simp_all add: comp_assoc[THEN sym]   A_out_tp B_in_tp B_out_tp C_in_tp)


        show "A ;; B ;; C = A ;; (B ;; C)"
          by (simp add: \<open>A ;; (B ;; C) = \<lparr>In = I', Out = O', Trs = Trs A \<parallel> [IB' @ IC' \<leadsto> IB' @ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICB] oo [OA' \<leadsto> OA'] \<parallel> (Trs B \<parallel> [ICB \<leadsto> ICB] oo [Out B @ ICB \<leadsto> OB' @ In C] oo [OB' \<leadsto> OB'] \<parallel> Trs C)\<rparr>\<close> \<open>A ;; B ;; C = \<lparr>In = I', Out = O', Trs = (Trs A \<parallel> [IB' \<leadsto> IB'] oo [Out A @ IB' \<leadsto> OAB @ In B] oo [OAB \<leadsto> OAB] \<parallel> Trs B) \<parallel> [IC' \<leadsto> IC'] oo [OAB @ Out B @ IC' \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C\<rparr>\<close> \<open>Trs A \<parallel> [IB' @ IC' \<leadsto> IB' @ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICB] oo [OA' \<leadsto> OA'] \<parallel> Trs B \<parallel> [ICB \<leadsto> ICB] oo [OA' @ Out B @ ICB \<leadsto> OA' @ OB' @ In C] oo [OA' @ OB' \<leadsto> OA' @ OB'] \<parallel> Trs C = Trs A \<parallel> [IB' @ IC' \<leadsto> IB' @ IC'] oo [Out A @ IB' @ IC' \<leadsto> OA' @ In B @ ICB] oo [OA' \<leadsto> OA'] \<parallel> (Trs B \<parallel> [ICB \<leadsto> ICB] oo [Out B @ ICB \<leadsto> OB' @ In C] oo [OB' \<leadsto> OB'] \<parallel> Trs C)\<close> calculation)

      qed


      (* former definition
      definition Parallel :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr"  (infixl "|||" 80) where
        "A ||| B = \<lparr>In = In A @ In B, Out = Out A @ Out B, Trs = Trs A \<parallel> Trs B\<rparr>"
      *)



      definition Parallel :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr"  (infixl "|||" 80) where
        "A ||| B = \<lparr>In = In A \<oplus> In B, Out = Out A @ Out B, Trs = [In A \<oplus> In B \<leadsto> In A @ In B] oo (Trs A \<parallel> Trs B) \<rparr>"

      lemma type_ok_Parallel: "type_ok A \<Longrightarrow> type_ok B  \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> type_ok (A ||| B)"
        by (simp add: type_ok_def Parallel_def   distinct_addvars)


      lemma Parallel_indep: "type_ok A \<Longrightarrow> type_ok B  \<Longrightarrow> set (In A) \<inter> set (In B) = {} \<Longrightarrow>
        A ||| B = \<lparr>In = In A @ In B, Out = Out A @ Out B, Trs = (Trs A \<parallel> Trs B) \<rparr>"
        apply (simp add: Parallel_def, safe)
        apply (simp add: addvars_def diff_distinct)
        apply (subgoal_tac "In A \<oplus> In B = In A @ In B")
        apply simp
        apply (subst distinct_id)
        apply (simp add: type_ok_def)
        apply (subst comp_id_left_a)
        apply (simp add: type_ok_def)
        apply simp
        by (simp add: addvars_def diff_distinct)


      lemma Parallel_assoc_gen: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> 
            A ||| B ||| C = A ||| (B ||| C)"
        proof -
          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"
          assume [simp]: "type_ok C"

          have [simp]: "TVs (In A) = TI (Trs A)"
            apply (subgoal_tac "type_ok A")
            apply (simp only: type_ok_def)
            by simp

          have [simp]: "distinct (In A)"
            apply (subgoal_tac "type_ok A")
            apply (simp only: type_ok_def)
            by simp

          have [simp]: "TVs (In B) = TI (Trs B)"
            apply (subgoal_tac "type_ok B")
            apply (simp only: type_ok_def)
            by simp

          have [simp]: "distinct (In B)"
            apply (subgoal_tac "type_ok B")
            apply (simp only: type_ok_def)
            by simp

          have [simp]: "TVs (In C) = TI (Trs C)"
            apply (subgoal_tac "type_ok C")
            apply (simp only: type_ok_def)
            by simp

          have [simp]: "distinct (In C)"
            apply (subgoal_tac "type_ok C")
            apply (simp only: type_ok_def)
            by simp

          have [simp]: "distinct (In A \<oplus> (In B \<oplus> In C))"
            by (simp add: distinct_addvars)

          have [simp]: "set (In A \<oplus> In B) \<subseteq> set (In A \<oplus> (In B \<oplus> In C))"
            apply (simp add: addvars_def set_diff)
            by blast

          have [simp]: "set (In C) \<subseteq> set (In A \<oplus> (In B \<oplus> In C))"
            apply (simp add: addvars_def set_diff)
            by blast

          have [simp]: "set (In A) \<subseteq> set (In A \<oplus> (In B \<oplus> In C))"
            by (simp add: addvars_def set_diff)

          have [simp]: "set (In B \<oplus> In C) \<subseteq> set (In A \<oplus> (In B \<oplus> In C))"
            by (simp add: addvars_def set_diff)

          have "Trs (A ||| B ||| C) = [In A \<oplus> (In B \<oplus> In C) \<leadsto> (In A \<oplus> In B) @ In C] oo ([In A \<oplus> In B \<leadsto> In A @ In B] oo Trs A \<parallel> Trs B) \<parallel> Trs C"
            by (simp add: Parallel_def addvars_assoc)
          also have "... = [In A \<oplus> (In B \<oplus> In C) \<leadsto> (In A \<oplus> In B) @ In C] oo 
              ([In A \<oplus> In B \<leadsto> In A @ In B] \<parallel> [In C \<leadsto> In C] oo Trs A \<parallel> Trs B \<parallel> Trs C)"
            apply (subst comp_parallel_distrib)
            by (simp_all)
          also have "... = ([In A \<oplus> (In B \<oplus> In C) \<leadsto> (In A \<oplus> In B) @ In C] oo [In A \<oplus> In B \<leadsto> In A @ In B] \<parallel> [In C \<leadsto> In C]) oo 
              Trs A \<parallel> Trs B \<parallel> Trs C"
            by (simp add: comp_assoc)
          also have "... = [In A \<oplus> (In B \<oplus> In C) \<leadsto> In A @ In B @ In C] oo Trs A \<parallel> Trs B \<parallel> Trs C"
            apply (rule_tac f = "\<lambda> X . X oo (Trs A \<parallel> Trs B \<parallel> Trs C)" in arg_cong)
            apply (simp add: addvars_assoc [THEN sym])
            by (subst switch_par_comp_Subst, simp_all add: distinct_addvars set_addvars Subst_eq)            
          also have "... = [In A \<oplus> (In B \<oplus> In C) \<leadsto> In A @ (In B @ In C)] oo 
              Trs A \<parallel> (Trs B \<parallel> Trs C)"
            by (simp add: par_assoc)
          also have "... = ([In A \<oplus> (In B \<oplus> In C) \<leadsto> In A @ (In B \<oplus> In C)] oo [In A \<leadsto> In A] \<parallel> [In B \<oplus> In C \<leadsto> In B @ In C]) oo
              Trs A \<parallel> (Trs B \<parallel> Trs C)"
            apply (rule_tac f = "\<lambda> X . X oo (Trs A \<parallel> (Trs B \<parallel> Trs C))" in arg_cong)
            apply (simp add: addvars_assoc [THEN sym])
            by (subst switch_par_comp_Subst, simp_all add: distinct_addvars set_addvars Subst_eq, auto)
          also have "... = [In A \<oplus> (In B \<oplus> In C) \<leadsto> In A @ (In B \<oplus> In C)] oo 
              (([In A \<leadsto> In A] oo Trs A) \<parallel> ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C))"
            apply (simp add: comp_assoc par_assoc)
            apply (subst comp_parallel_distrib)
            by (simp_all )
          also have "... = [In A \<oplus> (In B \<oplus> In C) \<leadsto> In A @ (In B \<oplus> In C)] oo 
               Trs A \<parallel> ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C)"
            apply (subst comp_id_switch)
            by simp_all
          also have "... = Trs (A ||| (B ||| C))"
            by (simp add: Parallel_def)

        show  "A ||| B ||| C = A ||| (B ||| C)"
          using Parallel_def addvars_assoc calculation by fastforce
      qed


      lemma length_TVs: "length (TVs x) = length x"
        by (induction x, simp_all)

      definition FB :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr" where
        "FB A = (let I = In A \<ominus> Var A A in let O' = Out A \<ominus> Var A A in 
          \<lparr>In = I, Out = O', Trs = (fb ^^ (length (Var A A))) ([Var A A @ I \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ O']) \<rparr>)"

      lemma Type_ok_FB: "type_ok A \<Longrightarrow> type_ok (FB A)"
        apply (simp add: type_ok_def FB_def Let_def Var_def, safe)
        apply (cut_tac t="TVs(Out A \<otimes> In A)" and ts="TVs ((In A \<ominus> Out A \<otimes> In A))" and ts'="TVs ((Out A \<ominus> Out A \<otimes> In A))" and
            S="([(Out A \<otimes> In A) @ (In A \<ominus> Out A \<otimes> In A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> (Out A \<otimes> In A) @ (Out A \<ominus> Out A \<otimes> In A)])" in TI_fb_fbtype_n)
        apply (simp add: fbtype_def)
        apply (subgoal_tac "length (TVs (Out A \<otimes> In A)) = length (Out A \<otimes> In A)")
        apply simp
        apply (simp add: length_TVs)
        apply (cut_tac t="TVs (Out A \<otimes> In A)" and ts="TVs (In A \<ominus> Out A \<otimes> In A)" and ts'="TVs (Out A \<ominus> Out A \<otimes> In A)" and
            S="([(Out A \<otimes> In A) @ (In A \<ominus> Out A \<otimes> In A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> (Out A \<otimes> In A) @ (Out A \<ominus> Out A \<otimes> In A)])" in TO_fb_fbtype_n)
        apply (simp add: fbtype_def)
        apply (subgoal_tac " length (TVs (Out A \<otimes> In A)) =  length (Out A \<otimes> In A)")
        apply simp
        apply (simp add: length_TVs)
        apply (simp add: distinct_diff)
        by (simp add: distinct_diff)

      lemma perm_var_Par: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (In A) \<inter> set (In B) = {} \<Longrightarrow> perm (Var (A ||| B) (A ||| B)) (Var A A @ Var B B @ Var A B @ Var B A)"
        apply (simp add: Parallel_indep Var_def append_inter)
        apply (frule_tac x = "Out A" in inter_append)
        apply (drule_tac x = "Out B" in inter_append)
        by (simp add: perm_def union_commute union_lcomm)

      lemma distinct_Parallel_Var[simp]: "type_ok A \<Longrightarrow> type_ok B  
        \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> distinct (Var (A ||| B) (A ||| B))"
        apply (simp add: Parallel_def Var_def append_inter, safe)
        apply (simp add: distinct_inter type_ok_def)
        apply (simp add: distinct_inter type_ok_def)
        using notin_inter by fastforce
(*
      lemma distinct_Parallel_Var[simp]: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (In A) \<inter> set (In B) = {} 
        \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> distinct (Var (A ||| B) (A ||| B))"
        apply (simp add: Parallel_indep Var_def append_inter, safe)
        sledgehammer
        apply (rule_tac x = "(Out A \<otimes> In A) @ (Out A \<otimes> In B)" in dist_perm, simp, safe)
        apply (rule distinct_inter, simp add: type_ok_def)
        apply (rule distinct_inter, simp add: type_ok_def)
        apply (simp add: set_inter, auto)
        apply (rule perm_sym)
        apply (rule inter_append, simp)
        apply (rule distinct_inter, simp add: type_ok_def)
        by (simp add: set_inter, auto)
*) 
      lemma distinct_Parallel_In[simp]: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> distinct (In (A ||| B))"
        apply (simp add: Parallel_def Var_def append_inter type_ok_def)
        using distinct_addvars by auto
(*
      lemma distinct_Parallel_In[simp]: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (In A) \<inter> set (In B) = {} \<Longrightarrow> distinct (In (A ||| B))"
        by (simp add: Parallel_indep Var_def append_inter type_ok_def)
*)
      lemma drop_assumption: "p \<Longrightarrow> True"
        by simp

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

(*
New proof
      theorem FP_IC_res_new: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (In A) \<inter> set (In B) = {} 
      \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> FB (A ||| B) = FB (FB (A) ;; FB (B))"
        proof -
          assume A [simp]: "set (In A) \<inter> set (In B) = {}"
          assume B [simp]: "set (Out A) \<inter> set (Out B) = {}"
          have [simp]: "In A \<oplus> In B = In A @ In B"
            by (simp add: addvars_distinct)
          assume "type_ok A"
          assume "type_ok B"
          have [simp]: "distinct (In A)" and [simp]: "distinct (In B)"
            using \<open>type_ok A\<close> type_ok_def apply auto[1]
            using \<open>type_ok B\<close> type_ok_def by auto[1]
          have [simp]: "TI (Trs A) = TVs (In A)" and "TO (Trs A) = TVs (Out A)"
            using \<open>type_ok A\<close> type_ok_def apply force
            using \<open>type_ok A\<close> type_ok_def by force
          have [simp]: "TI (Trs B) = TVs (In B)" and "TO (Trs B) = TVs (Out B)"
            using \<open>type_ok B\<close> type_ok_def apply force
            using \<open>type_ok B\<close> type_ok_def by force

          have [simp]: "In A \<ominus> Out A \<ominus> (Out B \<ominus> In B) = (In A \<ominus> Out A \<ominus> Out B)"
            apply (subst diff_notin, simp_all add: set_diff)
            using A by blast

          thm diff_commute

          have [simp]: "In B \<ominus> Out B \<ominus> (Out A \<ominus> In A) = (In B \<ominus> Out A \<ominus> Out B)"
            apply (subst diff_notin, simp_all add: set_diff diff_sym)
            using A by blast

          have [simp]: "Out A \<ominus> In A \<ominus> (In B \<ominus> Out B) = (Out A \<ominus> In A \<ominus> In B)"
            apply (subst diff_notin, simp_all add: set_diff)
            using B by blast

          have [simp]: "Out B \<ominus> In B \<ominus> (In A \<ominus> Out A) = (Out B \<ominus> In A \<ominus> In B)"
            apply (subst diff_notin, simp_all add: set_diff diff_sym)
            using B by blast

          have [simp]: "\<And> x y x' y' . (In A \<ominus> x \<ominus> y) \<oplus> (In B \<ominus> x' \<ominus> y') = (In A \<ominus> x \<ominus> y) @ (In B \<ominus> x' \<ominus> y')"
            apply (subst addvars_distinct, simp_all add: set_diff)
            using A by blast

          have [simp]: "\<And> x x' y' . (In A \<ominus> x) \<oplus> (In B \<ominus> x' \<ominus> y') = (In A \<ominus> x) @ (In B \<ominus> x' \<ominus> y')"
            apply (subst addvars_distinct, simp_all add: set_diff)
            using A by blast
          have [simp]: "distinct (In B \<ominus> Out A \<ominus> Out B)"
            by (simp add: distinct_diff)

          show ?thesis
            apply (simp add: Parallel_def FB_def Comp_def Let_def Var_def, safe)
            apply (simp_all add: diff_inter_left diff_inter_right)
            apply (simp_all add: addvars_minus diff_union distinct_id union_diff diff_addvars diff_redundant_a 
                diff_redundant_b diff_redundant_c diff_redundant_d)
            sorry
        qed
*)

      lemma  Dgr_eq: "In A = x \<Longrightarrow> Out A = y \<Longrightarrow> Trs A = S \<Longrightarrow>  \<lparr>In = x, Out = y, Trs = S\<rparr> = A"
        by auto

    lemma set_list_empty: "set x = {} \<Longrightarrow> x = []"
      by (induction x, simp_all)

    lemma [simp]: "(x \<ominus> x \<otimes> y) \<otimes> (y \<ominus> x \<otimes> y) = []"
      apply (rule set_list_empty)
      by (simp add: set_inter set_diff, auto)


      lemma Var_FB[simp]: "Var (FB A) (FB A) = []"
        by (simp add: FB_def Var_def Let_def)

      theorem FB_idemp: "type_ok A \<Longrightarrow> FB (FB A) = FB A"
        apply (subst FB_def)
        apply (simp add: Let_def diff_emptyset)
        apply (rule Dgr_eq, simp_all)
        by (metis (no_types, lifting) BaseOperationVars.type_ok_def BaseOperationVars_axioms Type_ok_FB comp_id_right comp_id_switch distinct_id)

      theorem FeedbackSerial: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (In A) \<inter> set (In B) = {} (*required*)
      \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> FB (A ||| B) = FB (FB (A) ;; FB (B))"
        proof -
          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"
          assume [simp]: "set (In A) \<inter> set (In B) = {}"
          assume [simp]: "set (Out A) \<inter> set (Out B) = {}"

          def I \<equiv> "(In (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B))"
          def O' \<equiv> "(Out (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B))"

          def IA' \<equiv> "In A \<ominus> Out A \<ominus> Out B"
          def IB' \<equiv> "In B \<ominus> Out A \<ominus> Out B"

          def IA'' \<equiv> "In A \<ominus> Out A"
          def IB'' \<equiv> "In B \<ominus> Out B"

          def OA' \<equiv> "Out A \<ominus> In A \<ominus> In B"
          def OB' \<equiv> "Out B \<ominus> In A \<ominus> In B"
          
          def OA'' \<equiv> "Out A \<ominus> In A"
          def OB'' \<equiv> "Out B \<ominus> In B"

          have [simp]: "TI (Trs A) = TVs (In A)"
            apply (subgoal_tac "type_ok A")
            apply (unfold type_ok_def)[1]
            by simp_all

          have [simp]: "TI (Trs B) = TVs (In B)"
            apply (subgoal_tac "type_ok B")
            apply (unfold type_ok_def)[1]
            by simp_all

          have [simp]: "TO (Trs A) = TVs (Out A)"
            apply (subgoal_tac "type_ok A")
            apply (unfold type_ok_def)[1]
            by simp_all

          have [simp]: "TO (Trs B) = TVs (Out B)"
            apply (subgoal_tac "type_ok B")
            apply (unfold type_ok_def)[1]
            by simp_all

          have I_simp:"I = IA' @ IB'"
            apply (simp add: I_def IA'_def IB'_def Parallel_indep Var_def diff_filter inter_filter)
            apply (subgoal_tac "[a\<leftarrow>In A . (a \<in> set (Out A) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B)) \<and> (a \<in> set (Out B) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B))] = [x\<leftarrow>In A . x \<notin> set (Out A) \<and> x \<notin> set (Out B)]")
            apply simp
            apply (drule drop_assumption, simp)
            apply (rule filter_cong, auto)
            by (rule filter_cong, auto)

          have In_simp: "(In (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B)) = IA' @ IB'"
            apply (simp add: IA'_def IB'_def Parallel_indep Var_def diff_filter inter_filter)
            apply (subgoal_tac "[a\<leftarrow>In A . (a \<in> set (Out A) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B)) \<and> (a \<in> set (Out B) \<longrightarrow> a \<notin> set (In A) \<and> a \<notin> set (In B))] = [x\<leftarrow>In A . x \<notin> set (Out A) \<and> x \<notin> set (Out B)]")
            apply simp
            apply (drule drop_assumption, simp)
            apply (rule filter_cong, auto)
            by (rule filter_cong, auto)

          have O'_simp: "O' = OA' @ OB'"
            by (simp add: O'_def OA'_def OB'_def Parallel_indep Var_def diff_inter_left union_diff diff_union)
            
          have Out_simp: "(Out (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B)) = OA' @ OB'" 
            by (simp add: OA'_def OB'_def Parallel_indep Var_def diff_inter_left union_diff diff_union)

          have [simp]: "distinct O'"
            apply (simp add: O'_def)
            apply (rule distinct_diff)
            apply (simp add: Parallel_def)
            apply (subgoal_tac "type_ok A")
            apply (subgoal_tac "type_ok B")
            apply  (unfold type_ok_def)[1]
            by (simp_all)

          have [simp]: "distinct I"
            apply (simp add: I_def Parallel_indep Var_def)
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply (subgoal_tac "type_ok A")
            apply (subgoal_tac "type_ok B")
            apply (simp add: type_ok_def)
            by (simp_all add: distinct_diff)
          

          have [simp]: "distinct IA'"
            apply (simp add: IA'_def)
            apply (rule distinct_diff)
            apply (subgoal_tac "type_ok A")
            apply (unfold "type_ok_def")[1]
            by (simp_all add: distinct_diff)

          have [simp]: "distinct IB'"
            apply (simp add: IB'_def)
            apply (rule distinct_diff)
            apply (subgoal_tac "type_ok A")
            apply (subgoal_tac "type_ok B")
            apply (unfold "type_ok_def")[1]
            by (simp_all add: distinct_diff)

          have [simp]: "TI (Trs (A ||| B)) = TVs (In (A ||| B))"
            by (simp add: Parallel_indep)

          have [simp]: "TO (Trs (A ||| B)) = TVs (Out (A ||| B))"
            by (simp add: Parallel_indep)
          
          have [simp]: "distinct (Out A)"
            apply (subgoal_tac "type_ok A")
            apply (unfold type_ok_def)[1]
            by simp_all
 
          have [simp]: "distinct (Out B)"
            apply (subgoal_tac "type_ok B")
            apply (unfold type_ok_def)[1]
            by simp_all

          have [simp]: "distinct (Var A A)"
            by (simp add: Var_def distinct_inter)

          have [simp]: "distinct (Var B B)"
            by (simp add: Var_def distinct_inter)

          have [simp]: "distinct (Var A B)"
            by (simp add: Var_def distinct_inter)

          have [simp]: "distinct (Var B A)"
            by (simp add: Var_def distinct_inter)

          have setI: "set I  = set (In A) \<union> set (In B) - (set (Out A) \<union> set (Out B))"
            by (simp add: I_def Parallel_indep Var_def set_diff set_inter, auto)

          have [simp]: "set (Var A A) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast
          have [simp]: "set (Var A B) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast

          have [simp]: "set (Var B A) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast

          have [simp]: "set (Var B B) \<inter> set I = {}"
            apply (simp add: Var_def setI set_inter)
            by blast

          have [simp]: "set (Var A B) \<inter> set (Var B A) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var B B) \<inter> set (Var A B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: " set (Var B B) \<inter> set (Var B A) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var A A) \<inter> set (Var B B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var A A) \<inter> set (Var A B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var A A) \<inter> set (Var B A) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var A B) \<inter> set (Var B B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (Out A) \<inter> set (Out B) = {}\<close> by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def Parallel_def set_diff)
            by blast

          have [simp]: "set (Var A B) \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def Parallel_def set_diff)
            by blast

          have [simp]: "set IA' \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def IA'_def Parallel_indep set_diff)
            by blast          

          have [simp]: "set IB' \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> (set (Var B A) \<union> set I))"
            apply (simp add: Var_def set_inter I_def IB'_def Parallel_indep set_diff)
            by blast 

          have [simp]: "distinct OA'"
            by (simp add: OA'_def distinct_diff)

          have [simp]: "distinct OB'" 
            by (simp add: OB'_def distinct_diff)

          have [simp]: "set (Var B A) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var B B) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: " set OA' \<inter> set (Var B B) = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set (Var B A) = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set OB' = {}"
            by (metis O'_simp \<open>distinct O'\<close> distinct_append)

          have [simp]: "set (Var A B) \<inter> set OA' = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A B) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A A) \<inter> set OA' = {}"
            apply (simp add: Var_def OA'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A A) \<inter> set OB' = {}"
            apply (simp add: Var_def OB'_def set_diff set_inter)
            by blast

          have [simp]: "set (Var B B) \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B B) \<union> (set (Var B A) \<union> set OB')))"
            apply (simp add: OA'_def OB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B B) \<union> (set (Var B A) \<union> set OB')))"
            apply (simp add: OA'_def OB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set O' \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B B) \<union> (set (Var B A) \<union> set OB')))"
            apply (simp add: O'_def OA'_def OB'_def Parallel_indep Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var A B) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var B B) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set IA' \<inter> set (Var B B) = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set IA' \<inter> set (Var A B) = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set IA' \<inter> set IB' = {}"
            apply (simp add: IA'_def IB'_def set_diff)
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply blast
            by simp

          have [simp]: "set (Var B A) \<inter> set IA' = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var B A) \<inter> set (Var B B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var B A) \<inter> set (Var A B) = {}"
            apply (simp add: Var_def set_inter)
            using \<open>set (In A) \<inter> set (In B) = {}\<close> by blast

          have [simp]: "set (Var B A) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var A A) \<inter> set IA' = {}"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast
          have [simp]: "set (Var A A) \<inter> set IB' = {}"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (In A) \<subseteq> set (Var A A) \<union> (set (Var B A) \<union> set IA')"
            apply (simp add: IA'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> (set (Var A B) \<union> set IB')"
            apply (simp add: IB'_def Var_def set_inter set_diff)
            by blast

          have [simp]: "set (Var A A) \<subseteq> set (Out A)"
            by (simp add: Var_def set_inter)

          have [simp]: "set (Var A B) \<subseteq> set (Out A)"
            by (simp add: Var_def set_inter)

          have [simp]: "set OA' \<subseteq> set (Out A)"
            apply (simp add: OA'_def set_diff)
            by blast

          have [simp]: "set (Var B B) \<subseteq> set (Out B)"
            by (simp add: Var_def set_inter)

          have [simp]: "set (Var B A) \<subseteq> set (Out B)"
            by (simp add: Var_def set_inter)

          have [simp]: "set OB' \<subseteq> set (Out B)"
            apply (simp add: OB'_def set_diff)
            by blast

          have [simp]: "set OB' \<inter> set (Var A A) = {}"
            apply (simp add: OB'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set OB' \<inter> set (Var A B) = {}"
            apply (simp add: OB'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set OB' \<inter> set OA' = {}"
            by (simp add: Int_commute)          

          have [simp]: "set (Var B A) \<inter> set (Var A A) = {} "
            by (simp add: Int_commute)          

          have [simp]: "set (Var B A) \<inter> set OA' = {}"
            by (simp add: Int_commute)          

          have [simp]: "set (Var B B) \<inter> set (Var A A) = {} "
            by (simp add: Int_commute)          

          have [simp]: "set (Var B B) \<inter> set OA' = {}"
            by (simp add: Int_commute)          

          have [simp]: "perm (Var B B @ Var A B @ Var B A @ I) (Var B A @ IA' @ Var B B @ Var A B @ IB')"
            by (simp add: I_simp perm_def union_lcomm)

          have [simp]: "perm (Var B B @ Var B A @ OB' @ Var A B @ OA') (Var A B @ OA' @ Var B B @ Var B A @ OB')"
            by (simp add: perm_def)

          have [simp]: "set IB' \<subseteq> set (Var A B) \<union> (set (Var B A) \<union> set I)"
            apply (simp add: I_simp)
            by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var A B) \<union> (set (Var B A) \<union> set I)"
            by blast

          have [simp]: "set IA' \<subseteq> set (Var A B) \<union> (set (Var B A) \<union> set I)"
            apply (simp add: I_simp)
            by blast

          have [simp]: "set IB' \<subseteq> set (Var B A) \<union> set I" 
            apply (simp add: I_simp)
            by blast

          have [simp]: "set IA' \<subseteq> set (Var B A) \<union> set I"
            apply (simp add: I_simp)
            by blast
          
          have [simp]: "set (Var A B) \<subseteq> set (Var B A) \<union> (set OB' \<union> (set (Var A B) \<union> set OA'))"
            by blast

          have [simp]: "set O' \<subseteq> set (Var B A) \<union> (set OB' \<union> (set (Var A B) \<union> set OA'))"
            apply (simp add: O'_simp)
            by safe

          have [simp]: "set IB' \<inter> set (Var B A) = {}"
            apply (simp add: IB'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set IB' \<inter> set IA' = {}"
            by (simp add: Int_commute)

          have [simp]: "set (Var A B) \<inter> set IA' = {}"
            by (simp add: Int_commute)

          have [simp]: "perm (Var B A @ I) (IB' @ Var B A @ IA')"
            by (simp add: I_simp perm_def)

          have [simp]: "perm (Var A B @ OA' @ Var B A @ OB') (Var B A @ OB' @ Var A B @ OA')"
            by (metis append_assoc perm_tp)

          have [simp]: "set (Var B A) \<subseteq> set OA' \<union> (set (Var B A) \<union> set OB')"
            by blast

          have [simp]: "set O' \<subseteq> set OA' \<union> (set (Var B A) \<union> set OB')"
            apply (simp add: O'_simp)
            by blast

          have [simp]: "set (Var B A) \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B A) \<union> set OB'))"
            by blast

          have [simp]: "set O' \<subseteq> set (Var A B) \<union> (set OA' \<union> (set (Var B A) \<union> set OB'))"
            apply (simp add: O'_simp)
            by blast

          have [simp]: "set (Var A B) \<inter> set O' = {}"
            by (simp add: O'_simp)

          have [simp]: "set OA' \<inter> set IB' = {}"
            apply (simp add: OA'_def IB'_def set_diff)
            by blast

          have [simp]: "set IA'' \<subseteq> set (Var B A) \<union> set IA'"
            apply (simp add: IA''_def IA'_def set_diff Var_def set_inter)
            by blast

          have [simp]: "perm (Var B A @ IA') IA''"
            proof -
              have A: "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) IA''"
                apply (simp add: IA''_def diff_filter inter_filter perm_def)
                by (metis filter_filter mset_compl_union)
 
              have B: "((In A \<ominus> Out A) \<otimes> Out B) = (In A \<otimes> Out B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp

              have C: "perm (In A \<otimes> Out B) (Out B \<otimes> In A)"
                apply (simp add: perm_def inter_filter)
                apply (subgoal_tac "distinct (Var B A)")
                apply (subgoal_tac "type_ok A")
                apply (simp only: Var_def type_ok_def)
                apply (metis Int_commute distinct_inter inter_filter set_eq_iff_mset_eq_distinct set_inter)
                by simp_all

              have D: "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B))"
                by (simp add: B C perm_union_left)

              have E: "perm ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B)) (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B))"
                by (simp only: D perm_sym)

              show "perm (Var B A @ IA') IA''"
                apply (simp add: Var_def IA'_def)
                apply (subgoal_tac "perm ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B)) (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B))")
                apply (subgoal_tac "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) IA''")
                apply (simp add: perm_def)
                by (simp_all only: E A )
            qed

          have [simp]: "perm (Var A B @ OA') OA''"
            proof -
              have A: "perm (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''"
                apply (simp add: OA''_def diff_filter inter_filter perm_def)
                by (metis filter_filter mset_compl_union)
              have B: "((Out A \<ominus> In A)) \<otimes> In B = (Out A \<otimes> In B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have C: "perm ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''"
                apply (subgoal_tac "perm (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''")
                apply (subgoal_tac "((Out A \<ominus> In A)) \<otimes> In B = (Out A \<otimes> In B)")
                apply auto
                apply (simp only: B)
                by (simp only: A)
              show "perm (Var A B @ OA') OA''"
                by (simp add: Var_def OA'_def C)
            qed           

          have [simp]: "perm (OA' @ Var A B) OA''"
            apply (subgoal_tac "perm (Var A B @ OA') OA''")
            apply (metis perm_def perm_tp)
            by simp

          have [simp]: "perm (Out A) (Var A A @ OA'')"
            by (simp add: OA''_def Var_def diff_filter inter_filter perm_def)

          have [simp]: "distinct OA''"
            by (simp add: OA''_def distinct_diff)

          have [simp]: "set (Var A A) \<inter> set OA'' = {}"
            apply (simp add: OA''_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set (Var A B) \<subseteq> set OA''"
            apply (simp add: OA''_def Var_def set_diff set_inter)
            by (simp add: Diff_Int_distrib2 inf.absorb_iff2 inf.left_commute)

         have [simp]: "set OA' \<subseteq> set OA''"
            apply (simp add: OA'_def OA''_def set_diff)
            by blast

         have [simp]: "perm (Var A B @ IB') IB''"
            proof -
              have A: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out B \<ominus> Out A)) IB''"
                apply (simp add: IB''_def diff_filter inter_filter perm_def)
                by (metis filter_filter mset_compl_union)

              have B: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) IB''"
                apply (subst diff_sym)
                by (simp add: A)
 
              have C: "((In B \<ominus> Out B) \<otimes> Out A) = (In B \<otimes> Out A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp

              have D: "perm (In B \<otimes> Out A) (Out A \<otimes> In B)"
                apply (simp add: perm_def inter_filter)
                apply (subgoal_tac "distinct (Var A B)")
                apply (subgoal_tac "type_ok B")
                apply (simp only: Var_def type_ok_def)
                apply (metis Int_commute distinct_inter inter_filter set_eq_iff_mset_eq_distinct set_inter)
                by simp_all

              have E: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B))"
                by (simp add: B C D perm_union_left)

              have F: "perm ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B)) (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B))"
                by (simp only: E perm_sym)

              show "perm (Var A B @ IB') IB''"
                apply (simp add: Var_def IB'_def)
                apply (subgoal_tac "perm ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B)) (((In B \<ominus> Out B) \<otimes> Out A) @(In B \<ominus> Out A \<ominus> Out B))")
                apply (subgoal_tac "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) IB''")
                apply (simp add: perm_def diff_sym)
                by (simp_all only: F B)
            qed

         have [simp]: "perm (Out B) (Var B B @ OB'')"
            by (simp add: OB''_def Var_def diff_filter inter_filter perm_def)

         have [simp]: "perm (OA'' @ IB') (Var A B @ OA' @ IB')"
            by (metis perm_union_left \<open>perm (Var A B @ OA') OA''\<close> append_assoc perm_sym)

         have [simp]: "perm (OA'' @ IB') (OA' @ Var A B @ IB')"
            by (metis perm_union_left \<open>perm (OA' @ Var A B) OA''\<close> append_assoc perm_sym)

         have [simp]: "perm (Var B A @ OB') OB''"
            proof -
              have A: "perm (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''"
                apply (simp add: OB''_def diff_filter inter_filter perm_def)
                by (metis filter_filter mset_compl_union)
              have B: "(Out B \<ominus> In B) \<otimes> In A = (Out B \<otimes> In A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have C: "perm ((Out B \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''"
                apply (subgoal_tac "perm (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''")
                apply (subgoal_tac "(Out B \<ominus> In B) \<otimes> In A = (Out B \<otimes> In A)")
                apply (simp add: diff_filter inter_filter)
                apply (simp only: B)
                by (simp only: A)
              show "perm  (Var B A @ OB') OB''"
                apply (simp add: Var_def OB'_def)
                apply (subst diff_sym)
                by (simp add: C)
            qed 

         have [simp]: "perm (Out A @ Out B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B) @ (Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
            proof -
              have A: "perm (Out A) ((Out A \<otimes> In A) @ (Out A \<ominus> In A))"
                by (simp add: diff_filter inter_filter perm_def)
              have B: "perm (Out A \<ominus> In A) (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (simp add: diff_filter inter_filter perm_def)
                by (metis filter_filter mset_compl_union)
              have C: "((Out A \<ominus> In A) \<otimes> In B) = (Out A \<otimes> In B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have D: "perm (Out A \<ominus> In A) ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out A \<ominus> In A) (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                apply (subgoal_tac "((Out A \<ominus> In A) \<otimes> In B) = (Out A \<otimes> In B)")
                apply (simp add: perm_def)
                apply (simp only: C)
                by (simp only: B)
              
              have E: "perm (Out A)  ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out A) ((Out A \<otimes> In A) @ (Out A \<ominus> In A))")
                apply (subgoal_tac "perm (Out A \<ominus> In A) ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                apply (simp add: perm_def)
                apply (simp only: D)
                by (simp only: A)

              have F: "perm (Out B) ((Out B \<otimes> In B) @ (Out B \<ominus> In B))"
                by (simp add: diff_filter inter_filter perm_def)
              have G: "perm (Out B \<ominus> In B) (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subst diff_sym)
                apply (simp add: diff_filter inter_filter perm_def)
                by (metis filter_filter mset_compl_union)
              have H: "((Out B \<ominus> In B) \<otimes> In A) = (Out B \<otimes> In A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have I: "perm (Out B \<ominus> In B) ((Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out B \<ominus> In B) (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                apply (subgoal_tac "((Out B \<ominus> In B) \<otimes> In A) = (Out B \<otimes> In A)")
                apply (simp add: perm_def)
                apply (simp only: H)
                by (simp only: G)
              
              have J: "perm (Out B)  ((Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out B) ((Out B \<otimes> In B) @ (Out B \<ominus> In B))")
                apply (subgoal_tac "perm (Out B \<ominus> In B) ((Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                apply (simp add: perm_def)
                apply (simp only: I)
                by (simp only: F)
             
             show "perm (Out A @ Out B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B) @ (Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
              apply (subgoal_tac "perm (Out A)  ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
              apply (subgoal_tac "perm (Out B)  ((Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
              apply (simp add: perm_def union_assoc)
              apply (simp only: J)
              by (simp only: E)
          qed

         have [simp]: "set IB'' \<subseteq> set (Var A B) \<union> set IB'"
            apply (simp add: IB''_def IB'_def set_diff Var_def set_inter)
            by blast

         have [simp]: "distinct OB''"
            apply (simp add: OB''_def)
            apply (subgoal_tac "type_ok B")
            apply (simp only: type_ok_def distinct_diff)
            by simp

         have [simp]: "set (Var B B) \<inter> set OB'' = {}"
            apply (simp add: Var_def OB''_def set_inter set_diff)
            by blast

         have [simp]: "set (Var B A) \<subseteq> set OB''"
            apply (simp add: Var_def OB''_def set_inter set_diff)
            by (metis (no_types, hide_lams) Diff_Diff_Int Diff_Int_distrib Diff_eq_empty_iff Int_commute \<open>set (In A) \<inter> set (In B) = {}\<close> equalityI inf.cobounded2)
         
         have [simp]: "set OB' \<subseteq> set OB''"
            apply (simp add: OB'_def OB''_def)
            by (metis DiffE DiffI set_diff subsetI)


         have IA''_simp: "IA'' = (In A \<ominus> Var A A)"
            by (simp add: IA''_def Var_def diff_inter_right)

         have OA''_simp: "OA'' = (Out A \<ominus> Var A A)"
            by (simp add: OA''_def Var_def diff_inter_left)

         have IB''_simp: "IB'' = (In B \<ominus> Var B B)"
            by (simp add: IB''_def Var_def diff_inter_right)

         have OB''_simp: "OB'' = (Out B \<ominus> Var B B)"
            by (simp add: OB''_def Var_def diff_inter_left)

         have [simp]: "TI (Trs (FB A)) = TVs IA''"
            apply (simp add: FB_def Let_def IA''_simp)
            apply (cut_tac t="TVs (Var A A)" and ts="TVs(In A \<ominus> Var A A)" and ts'="TVs(Out A \<ominus> Var A A)" and
                S="([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])" in  TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            apply (simp)
            by (simp add: length_TVs)

         have [simp]: "TO (Trs (FB A)) = TVs OA''"
            apply (simp add: FB_def Let_def OA''_simp)
            apply (cut_tac t="TVs (Var A A)" and ts="TVs(In A \<ominus> Var A A)" and ts'="TVs(Out A \<ominus> Var A A)" and
                S="([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])" in  TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            apply simp
            by (simp add: length_TVs)


         have [simp]: "set OA'' \<inter> set IB' = {}"
            apply (simp add: OA''_def IB'_def set_diff)
            by blast

         have [simp]: "TI (Trs (FB B)) = TVs IB''"
            apply (simp add: FB_def Let_def IB''_simp)
            apply (cut_tac t="TVs (Var B B)" and ts="TVs(In B \<ominus> Var B B)" and ts'="TVs(Out B \<ominus> Var B B)" and
                S="([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])" in  TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            apply (simp)
            by (simp add: length_TVs)

         have [simp]: "TO (Trs (FB B)) = TVs OB''"
            apply (simp add: FB_def Let_def OB''_simp)
            apply (cut_tac t="TVs (Var B B)" and ts="TVs(In B \<ominus> Var B B)" and ts'="TVs(Out B \<ominus> Var B B)" and
                S="([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])" in  TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            apply (simp)
            by (simp add: length_TVs)

         have legth_Var_Parralel: "length (Var (A ||| B) (A ||| B)) = length (Var B A) + length (Var A B) + length (Var B B) + length (Var A A)"
            apply (simp add: Parallel_indep Var_def append_inter)
            apply (subgoal_tac "perm (Out A \<otimes> In A @ In B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B))")
            apply (simp add: perm_length)
            apply (subgoal_tac "perm (Out B \<otimes> In A @ In B) ((Out B \<otimes> In A) @ (Out B \<otimes> In B))")
            apply (simp add: perm_length)
            apply (simp add: inter_append)
            by (simp add: inter_append)

          have [simp]: "TI ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) = TVs (Var B A) @ TVs IA'"
            apply (cut_tac t="(TVs (Var A A))" and S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and ts="TVs(Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            by (simp_all add:  length_TVs)

          have [simp]: "TO ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) = TVs (Var A B) @ TVs OA'"
            apply (cut_tac t="(TVs (Var A A))" and S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and ts="TVs(Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var A A) = length (TVs (Var A A))")
            apply (simp add: TO_fb)
            by (simp add: length_TVs)

          have [simp]: "TI ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) = TVs (Var A B) @ TVs IB'"
            apply (cut_tac t="(TVs (Var B B))" and S="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" in TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var B B) = length (TVs (Var B B))")
            apply (simp add: TI_fb)
            by (simp add:  length_TVs)
          
          have [simp]: "TO ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) = TVs (Var B A) @ TVs OB'"
            apply (cut_tac t="(TVs (Var B B))" and S="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" in TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var B B) = length (TVs (Var B B))")
            apply (simp add: TO_fb)
            by (simp_all add:  length_TVs)

          have [simp]: "set OA' \<inter> set (Var A B) = {}"
            apply (simp add: OA'_def Var_def set_diff set_inter)
            by blast

          have [simp]: "set OA' \<inter> set OB'' = {}"
            apply (simp add: OA'_def OB''_def set_diff)
            by (simp add: Diff_Int_distrib inf.commute)

          have In_FB_A_simp: "In (FB A) = IA''"
            by (simp add: FB_def Let_def Var_def IA''_def diff_inter_left diff_inter_right)

          have Out_FB_A_simp: "Out (FB A) = OA''"
            by (simp add: FB_def Let_def Var_def OA''_def diff_inter_left diff_inter_right)

          have In_FB_B_simp: "In (FB B) = IB''"
            by (simp add: FB_def Let_def Var_def IB''_def diff_inter_left diff_inter_right)

          have Out_FB_B_simp: "Out (FB B) = OB''"
            by (simp add: FB_def Let_def Var_def OB''_def diff_inter_left diff_inter_right)

          have [simp]: "(IB'' \<ominus> Var (FB A) (FB B)) = IB'"
            apply (simp add: FB_def Let_def Var_def IB''_def IB'_def diff_inter_right diff_inter_left)
            apply (subst diff_sym)
            apply (subst diff_notin)
            by (simp_all add: Int_commute)

          have [simp]:"(OA'' \<ominus> Var (FB A) (FB B)) = OA'"
            apply (simp add: FB_def Let_def Var_def OA''_def OA'_def diff_inter_right diff_inter_left)
            apply (subst diff_notin)
            apply (simp add: set_diff)
            apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
            apply blast
            by simp_all

          have[simp]: "set IA'' \<inter> set IB' = {}"
            apply (simp add: IA''_def IB'_def set_diff)
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply blast
            by simp

          have [simp]: "IA'' \<oplus> IB' = IA'' @ IB'"
            by (simp add: addvars_distinct)

          have [simp]: "distinct IA''"
            apply (simp add: IA''_def)
            apply (subgoal_tac "type_ok A")
            apply (simp only: type_ok_def distinct_diff)
            by simp

          have [simp]: "Trs (FB A) \<parallel> ID (TVs IB') oo [OA''@ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) = Trs (FB (A) ;; FB (B))"
            apply (simp add: Comp_def Let_def In_FB_A_simp Out_FB_A_simp In_FB_B_simp Out_FB_B_simp)
            by (simp add: distinct_id)
         
          have In_FB_simp: "In (FB A ;; FB B) = IA'' @ IB'"
            by (simp add: Comp_def In_FB_A_simp Out_FB_A_simp In_FB_B_simp Out_FB_B_simp)

          have Out_FB_simp: "Out (FB A ;; FB B) = OA' @ OB''"
            by (simp add: Comp_def In_FB_A_simp Out_FB_A_simp In_FB_B_simp Out_FB_B_simp)

          have Var_FB_simp: "(Var (FB A ;; FB B) (FB A ;; FB B)) = Var B A"
            apply (simp add: Var_def In_FB_simp Out_FB_simp)
            apply (simp add: append_inter)
            apply (simp add: OA'_def OB''_def IA''_def IB'_def)
            apply (subgoal_tac "((Out A \<ominus> In A \<ominus> In B) \<otimes> (In A \<ominus> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) = []")
            apply simp
            apply (subgoal_tac "(Out B \<ominus> In B) \<otimes> (In A \<ominus> Out A) @ (In B \<ominus> Out A \<ominus> Out B) = (Out B \<ominus> In B) \<otimes> (In A \<ominus> Out A)")
            apply simp
            apply (subst inter_diff_distrib)
            apply (subgoal_tac "Out B \<otimes> (In A \<ominus> Out A) = (Out B \<otimes> In A)")
            apply simp
            apply (subgoal_tac "In B \<otimes> (In A \<ominus> Out A) =[]")
            apply (simp add: diff_emptyset)
            apply (subgoal_tac "set (In B) \<inter> set(In A) = {}")
            apply (simp add: empty_inter_diff)
            apply (simp add: Int_commute)
            apply (subgoal_tac "set (Out B) \<inter> set (Out A) = {}")
            apply (subst inter_diff_empty)
            apply simp
            apply simp
            apply (simp add: Int_commute)
            apply (subst inter_addvars_empty)
            apply (simp add: set_diff)
            apply blast
            apply simp
            apply (subst empty_inter)
            apply (simp add: set_diff)
            apply blast
            by simp

          have [simp]: "(IA'' @ IB' \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = IA' @ IB'"
            apply (simp only: Var_FB_simp)
            apply (simp add: Var_def IA''_def IB'_def IA'_def)
            apply (simp add: union_diff)
            apply (subst diff_sym)
            apply (simp add: diff_inter_right)
            apply (subst diff_sym)
            apply (subst(5) diff_disjoint)
            apply (simp add: set_diff set_inter)
            apply blast
            by simp

          have [simp]: "(In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = IA' @ IB'"
            by (simp add: In_FB_simp)

          have [simp]: "(OA' @ OB'' \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = O'"
            apply (simp only: Var_FB_simp Out_FB_simp)
            apply (simp add: OA'_def OB''_def Var_def O'_simp OB'_def)
            apply (simp add: union_diff)
            apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
            apply (subst diff_inter_empty)
            apply (simp only: set_diff)
            apply blast
            apply (subst(2) diff_sym)
            apply (subst diff_inter_left)
            by simp_all

          have [simp]: "(Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) = O'"
            by (simp add: Out_FB_simp)
   

          have aa: "perm ((((Var A A @ Var B B) @ Var A B) @ Var B A) @ I) (Var (A ||| B) (A ||| B) @ I)"
            apply (subgoal_tac "perm (((Var A A @ Var B B) @ Var A B) @ Var B A) (Var (A ||| B) (A ||| B))")
            apply (subst perm_union_left)
            apply simp_all
            apply (subgoal_tac "type_ok A")
            apply (subgoal_tac "type_ok B")
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply (simp add: perm_var_Par perm_sym)
            by simp_all

         
          have "FB (A ||| B) = 
            \<lparr>In = I, Out = O', Trs = (fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'])  \<rparr>"
            (is "_ = \<lparr>In=I,Out=O',Trs = ?T\<rparr>")

            by (simp add: FB_def Let_def I_def O'_def) 

          have "?T = (fb ^^ length (Var (A ||| B) (A ||| B))) (
              [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] )" (is "_ = ?Fb (?Sa oo (?Sb oo ?Tr oo ?Sc) oo ?Sd)")
            apply (rule fb_perm [THEN sym])
            apply (simp_all add: perm_var_Par)
            apply (simp add: I_def, safe)
            apply (simp add: set_diff)
            apply (simp add: O'_def Var_def set_inter set_diff)
            by (simp add: fbtype_def)
          also have "... = ?Fb ((?Sa oo ?Sb) oo ?Tr oo (?Sc oo ?Sd))"
            apply (rule_tac f = "?Fb" in arg_cong)
            by (simp add: comp_assoc)
          also have "... = ?Fb ([(Var A A @ Var B B @ Var A B @ Var B A) @ I  \<leadsto> In (A ||| B)] oo ?Tr oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])"
            apply (subst switch_comp, simp_all)
            apply (unfold append_assoc [THEN sym])
            apply (simp only: aa)
            apply (simp add: Var_def Parallel_def set_addvars set_inter)
            apply auto [1]
            
              apply (simp add: setI)
              apply (simp add: setI)
              apply (simp add: perm_var_Par [THEN perm_sym])
            apply (subst switch_comp, simp_all add: Var_def distinct_inter set_inter setI Parallel_def O'_def)
            apply (simp add: perm_def mset_inter_diff [THEN sym])
            by (auto simp add: set_addvars set_diff set_inter)
          also have "... = ?Fb ([Var A A @ Var B B @ Var A B @ Var B A @ I  \<leadsto> In A @ In B] oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O'])" (is "?Lhs = ?Fc ?SS")
            by (simp add: Parallel_indep)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               ([Var A A @ Var B B @ Var A B @ Var B A @ I  \<leadsto> In A @ In B] oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O']))))"
            apply (simp add: legth_Var_Parralel)
            by (simp add: funpow_add)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               (([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B]) 
               oo ?Tr oo [Out A @ Out B \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']))))"
            apply (subgoal_tac "[Var A A @ Var B B @ Var A B @ Var B A @ I \<leadsto> In A @ In B] = [Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B]")
            apply simp
            apply (subst par_switch)
            apply (simp_all)
            apply (subst switch_comp)
            apply (simp_all add: perm_union_right)
            by (simp add: Var_def set_inter IB'_def set_diff IA'_def, auto)
            
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               (([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B]) 
               oo ?Tr oo ([Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) )))) "
            apply (subgoal_tac "[Out A @ Out B \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] = [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']")
            apply simp
            apply (subst par_switch)
            apply (simp_all)
            apply (subst switch_comp)
            apply (simp_all)
            apply (simp add: Var_def OA'_def OB'_def)
            by (simp add: Var_def set_inter IB'_def set_diff IA'_def OB'_def OA'_def O'_def Parallel_def, auto)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B] 
               oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) ))) "
            apply (subst comp_assoc[THEN sym])
            apply (simp add:   Parallel_indep)
            using Parallel_indep TO_comp \<open>TI (Trs (A ||| B)) = TVs (In (A ||| B))\<close> \<open>TO (Trs (A ||| B)) = TVs (Out (A ||| B))\<close> apply auto[1]
            apply (subst comp_assoc)
            apply simp_all
            apply (simp add: Parallel_indep)
            apply (subst comp_assoc)
            apply (simp_all)
            by (simp_all add:   Parallel_indep)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) 
               (ID (TVs (Var A A)) \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo  ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B] 
               oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo ID (TVs (Var A A)) \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) ))) "
            apply (subst distinct_id)
            apply simp_all
            apply (subst distinct_id)
            by simp_all
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) (
              [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo
                ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB'  \<leadsto> In A @ In B] 
                  oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'])) oo 
               [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']) ))" (is "_ = ?Fc (?Sf oo _ oo ?Sh)")
            apply (cut_tac A= "[Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB']" and B = "[Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']" and tsa = "TVs (Var A A)"
              and S="([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'])" in fb_indep)
            apply (simp add: fbtype_def)
            apply safe
            apply (simp_all add: Parallel_indep)
            apply (subgoal_tac "length (Var A A) = length (TVs (Var A A))")
            apply simp
            by (simp add: length_TVs)
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB'  \<leadsto> In B]  oo ?Tr oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'])) 
              oo ?Sh)"
            apply (subst par_switch)
            by simp_all 
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB'  \<leadsto> In B]  oo ?Tr oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']))
              oo ?Sh)"
            apply (subst(3) par_switch)
            by simp_all
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB'  \<leadsto> In B]  oo (Trs A \<parallel> Trs B) oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']))
              oo ?Sh)"
            by (simp add: Parallel_indep)
          also have "... = ?Fc (?Sf oo (
                (fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])))
              oo ?Sh)"  
            by (simp add: comp_parallel_distrib)
          also have "... = ?Fc (?Sf oo 
                ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) \<parallel> ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])
              oo ?Sh)"
            apply (cut_tac S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and T="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" 
              and tsa= "TVs (Var A A)" and ts="TVs (Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in fb_gen_parallel)
            apply (simp add: fbtype_def )
            apply (subgoal_tac "length (Var A A)= length (TVs (Var A A))")
            apply simp
            by (simp add: length_TVs)
          also have "... = ?Fc (?Sf oo 
                ( [Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB']
                )
              oo ?Sh)"
            apply (cut_tac x="Var B A @ IA'" and y="Var B B @ Var A B @ IB'" and u="Var B B @ Var B A @ OB'" and v="Var A B @ OA'" and 
              S="((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']))" and 
              T="([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" in switch_par)
            by (simp_all)
          also have "... = ?Fc 
                ( (?Sf oo [Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA']) oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo ?Sh) )"
            by (simp add: comp_assoc_middle_ext)
          also have "... = ?Fc 
                ( [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo ?Sh) )"
            apply (subst switch_comp)
            apply (simp_all)
            by (auto simp add: IA'_def IB'_def)
          also have "... = ?Fc 
                ( [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O'] )"
            apply (subst switch_comp)
            by (simp_all)
          also have  "... = ?Fc 
                ( ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O'] )"
            apply (subst par_switch[THEN sym])
            apply simp_all
            apply (subst distinct_id)
            by simp_all
          also have  "... = ?Fc 
                ( ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                  ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  ID (TVs (Var B B)) \<parallel> [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'] )"
            apply (subst (2) par_switch[THEN sym])
            apply simp_all
            apply (subst distinct_id)
            by simp_all
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) 
                ( [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                    ((fb ^^ length (Var B B)) (([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])))) oo
                  [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))" 
            apply (cut_tac tsa="TVs (Var B B)" and A= "[Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA']" and B="[Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']" and
                S = "([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel>
                  (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" in fb_indep)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            by (simp_all add: length_TVs)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) 
                ( [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                    ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))"  (is "_ = ?Fd (?Sk oo ?Sl \<parallel> ?Sm oo ?Sn) " )             
            apply (cut_tac tsa="TVs(Var B B)" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" and 
                S="([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" and
                T= "(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" in fb_gen_parallel)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            by (simp_all add: length_TVs)
          also have "... = ?Fd (?Sk oo 
                ([Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo ?Sm \<parallel> ?Sl oo [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA']) oo 
                ?Sn)"
            apply (cut_tac x="Var A B @ IB'" and y="Var B A @ IA'" and u="Var A B @ OA'" and v="Var B A @ OB'" and
                T="(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" and
                S="(fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" in switch_par)
            by simp_all
          also have "... = ?Fd (
                (?Sk oo [Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB']) oo 
                  ?Sm \<parallel> ?Sl oo 
                ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo ?Sn))"
            by (simp add: comp_assoc_middle_ext)
          also have "... = ?Fd (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl oo 
                ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo ?Sn))"
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (auto simp add: IA'_def IB'_def)
          also have "... = ?Fd (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl oo 
                [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var A B @ Var B A @ O'])"
            apply (subst switch_comp)
            by simp_all

           also have "... = ?Fd (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl oo 
                ID (TVs (Var A B)) \<parallel> [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst(2) par_switch[THEN sym])
            apply simp_all
            by (simp add: distinct_id)


          also have "... = (fb ^^ length (Var B A)) (((fb ^^ length (Var A B)) (
                [Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo 
                  ?Sm \<parallel> ?Sl)) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (cut_tac tsa="TVs(Var A B)" and
                S="([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo
                  (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel>
                  (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']))" and 
                B="[OA' @ Var B A @ OB' \<leadsto> Var B A @ O']" in fb_indep_right)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A B)) = length (Var A B)")
            by (simp_all add: length_TVs)
          also have "... = (fb ^^ length (Var B A))
                (?Sm \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (cut_tac u="Var A B" and x="Var B A @ IA'" and x'="IB'" and y="OA'" and y'="Var B A @ OB'" and
               A="(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" and
               B="(fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" in fb_par_serial)
            apply simp_all
            by (simp add: I_simp)
          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA'']) oo [Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (auto simp add: IA''_def Var_def set_inter set_diff)

          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo [Var A A @ IA'' \<leadsto> In A]) oo Trs A oo ([Out A \<leadsto> Var A A @ OA''] oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA'])) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst (3) switch_comp, simp_all)
            by (auto simp add: OA''_def OA'_def Var_def set_inter set_diff)

          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            by (simp add: comp_assoc [THEN sym])
          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst par_switch)
            by simp_all
          also have "... = (fb ^^ length (Var B A))
                ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A \<leadsto> Var A A] \<parallel> [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (subst(3) par_switch)
            by simp_all
          also have "... = (fb ^^ length (Var B A))
                (([Var B A @ IA' \<leadsto> IA''] oo (fb ^^ length (Var A A)) ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])"
            apply (cut_tac tsa="TVs ((Var A A))" and A="[Var B A @ IA' \<leadsto> IA'']" and B="[OA'' \<leadsto> Var A B @ OA']" and
                S="([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA''])" in fb_indep)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            apply (simp add: distinct_id)
            by (simp add: length_TVs)
          also have "... = (fb ^^ length (Var B A))
                (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB(A)) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo 
                [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ?Sl oo
                [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])" (is "_ = ?Fe (?So oo ID (TVs OA') \<parallel> ?Sl oo ?Sp)")
            apply (simp add: FB_def Let_def)
            apply (subgoal_tac "IA'' = (In A \<ominus> Var A A)")
            apply (subgoal_tac "OA'' = (Out A \<ominus> Var A A)")
            apply simp
            by (simp_all add: OA''_def IA''_def Var_def diff_inter_left diff_inter_right)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])
                oo ?Sp)"
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (auto simp add: Var_def IB'_def IB''_def set_inter set_diff)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo ([Out B \<leadsto> Var B B @ OB'' ] oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB']))
                oo ?Sp)"
            apply (subst(3) switch_comp)
            apply simp_all
            by (auto simp add: Var_def OB'_def OB''_def set_inter set_diff)

          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB'])
                oo ?Sp)"
            by (simp add: comp_assoc [THEN sym] )
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB'])
                oo ?Sp)"
            apply (subst par_switch)
            by simp_all
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo [Var B B \<leadsto> Var B B] \<parallel> [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)"
            apply (subst(3) par_switch)
            by simp_all
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo (fb ^^ length (Var B B)) ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'' ]) oo  [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)"
            apply (cut_tac tsa="TVs (Var B B)" and A="[Var A B @ IB' \<leadsto> IB'']" and B="[OB'' \<leadsto> Var B A @ OB']" and
                S="([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB''])"in fb_indep)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            apply (simp add: distinct_id)
            by (simp add: length_TVs)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo  [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)" (is "_ = ?Fe (?Sq oo ?Sr oo ?St oo ?Sp)")
            apply (subst(3) FB_def)
            apply (simp add: Let_def)
            apply (subgoal_tac "IB'' = (In B \<ominus> Var B B)")
            apply (subgoal_tac "OB'' = (Out B \<ominus> Var B B)")
            apply simp
            by (simp_all add: OB''_def IB''_def Var_def diff_inter_left diff_inter_right)
          also have "... = ?Fe (
                ([Var B A @ IA' \<leadsto> IA''] \<parallel> ID (TVs IB') oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB')) oo 
                ?Sr oo ?St oo ?Sp)"
            by (simp add: distinct_id[THEN sym] par_id_comp)
          also have "... = ?Fe (
                ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB')) oo 
                ?Sr oo ?St oo ?Sp)"
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (
                ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA''@ IB' \<leadsto> Var A B @ OA'@ IB']) oo 
                ?Sr oo ?St oo ?Sp)" (is "_=?Fe (?Ss oo ?Sr oo ?St oo ?Sp)")
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (?Ss oo ?Sr oo
                (ID (TVs OA') \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo
                ?Sp)"
            by (simp add: distinct_id[THEN sym] id_par_comp)
          also have "... = ?Fe (?Ss oo ?Sr oo
                ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo
                ?Sp)"            
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (?Ss oo ?Sr oo
                ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo [OA' @ OB'' \<leadsto> OA' @ Var B A @ OB']) oo
                ?Sp)"  
            by (simp add: distinct_id[THEN sym] par_switch)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                ([OA''@ IB' \<leadsto> Var A B @ OA'@ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))"  
             by (simp add: comp_assoc  )
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                ([OA''@ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))"  
            apply (subst switch_comp, simp_all)
            by (auto simp add: OA'_def Var_def IB'_def)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                [OA''@ IB' \<leadsto> OA' @ IB''] oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))"  
            apply (subst switch_comp, simp_all)
            by (auto simp add: OA'_def Var_def IB''_def IB'_def set_diff set_inter)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo 
                [OA''@ IB' \<leadsto> OA' @ IB''] oo
                ID (TVs OA') \<parallel> Trs (FB B) oo 
                [OA' @ OB'' \<leadsto> Var B A @ O'])"  
            by (simp add: switch_comp perm_sym perm_union_right)
          also have "... = ?Fe (
                [Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo 
                (Trs (FB (A) ;; FB (B))) oo
                [OA' @ OB'' \<leadsto> Var B A @ O'])"
             by (simp add: comp_assoc)
          also have "... = Trs (FB (FB (A) ;; FB (B)))"
            apply (subst(3) FB_def)
            apply (simp add: Let_def In_FB_simp Out_FB_simp)
            by (simp add: Var_FB_simp)



       finally show "FB (A ||| B) = FB (FB (A) ;; FB (B))"
          proof -
            have "FB (A ||| B) = \<lparr>In = In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B), Out = Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B), Trs = (fb ^^ length (Var (FB A ;; FB B) (FB A ;; FB B))) ([Var (FB A ;; FB B) (FB A ;; FB B) @ (In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) \<leadsto> In (FB A ;; FB B)] oo Trs (FB A ;; FB B) oo [Out (FB A ;; FB B) \<leadsto> Var (FB A ;; FB B) (FB A ;; FB B) @ (Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B))])\<rparr>"
              
              using I_simp In_FB_simp Out_FB_simp Var_FB_simp \<open>(fb ^^ length (Var (A ||| B) (A ||| B))) ([(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']) = (fb ^^ length (Var (A ||| B) (A ||| B))) ([Var A A @ Var B B @ Var A B @ Var B A @ I \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O'])\<close> \<open>(fb ^^ length (Var (A ||| B) (A ||| B))) ([(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']) = (fb ^^ length (Var (A ||| B) (A ||| B))) ([(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo ([Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'] oo [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']))\<close> \<open>(fb ^^ length (Var (A ||| B) (A ||| B))) ([(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo ([Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'] oo [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])) = (fb ^^ length (Var (A ||| B) (A ||| B))) ([(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])\<close> \<open>(fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) = (fb ^^ length (Var (A ||| B) (A ||| B))) ([(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])\<close> \<open>(fb ^^ length (Var (A ||| B) (A ||| B))) ([Var A A @ Var B B @ Var A B @ Var B A @ I \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A @ Var B B @ Var A B @ Var B A @ I \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O']))))\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo (fb ^^ length (Var A A)) ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo (fb ^^ length (Var B B)) ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' \<leadsto> IA''] \<parallel> ID (TVs IB') oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo ([Out B \<leadsto> Var B B @ OB''] oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB'])) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> Var B B @ IB''] oo [Var B B @ IB'' \<leadsto> In B] oo Trs B oo ([Out B \<leadsto> Var B B @ OB''] oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB'])) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [Var B B @ OB'' \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [Var B B \<leadsto> Var B B] \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B \<leadsto> Var B B] \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [Var B B \<leadsto> Var B B] \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo Trs (FB A) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo (fb ^^ length (Var B B)) ([Var B B @ IB'' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ OB'']) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo [Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo [Var A A @ IA'' \<leadsto> In A] oo Trs A oo ([Out A \<leadsto> Var A A @ OA''] oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA'])) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo [Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> Var A A @ IA''] oo [Var A A @ IA'' \<leadsto> In A] oo Trs A oo ([Out A \<leadsto> Var A A @ OA''] oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA'])) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A @ OA'' \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A \<leadsto> Var A A] \<parallel> [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B A @ IA' \<leadsto> IA''] oo ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [Var A A \<leadsto> Var A A] \<parallel> [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) (([Var B A @ IA' \<leadsto> IA''] oo (fb ^^ length (Var A A)) ([Var A A @ IA'' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ OA'']) oo [OA'' \<leadsto> Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) (ID (TVs (Var A A)) \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo ID (TVs (Var A A)) \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A @ Var B B @ Var A B @ Var B A @ I \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var B B @ Var A B @ Var B A @ O'])))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']))))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) (ID (TVs (Var A A)) \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo ID (TVs (Var A A)) \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo ([Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ((fb ^^ length (Var A A)) ([Var A A \<leadsto> Var A A] \<parallel> [Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo [Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo ([Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A A \<leadsto> Var A A] \<parallel> [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) (ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo ID (TVs (Var B B)) \<parallel> [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo (fb ^^ length (Var B B)) (([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) (ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) (ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo ID (TVs (Var B B)) \<parallel> [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo ([Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo [Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> In A @ In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> Var A A @ Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs (A ||| B) oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs (A ||| B) oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs A \<parallel> Trs B oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] \<parallel> [Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs A \<parallel> Trs B oo [Out A \<leadsto> Var A A @ Var A B @ OA'] \<parallel> [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) (([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo ([Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var B B @ Var A B @ IB'] oo [Var B A @ IA' @ Var B B @ Var A B @ IB' \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O']))))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo ([Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ OA' @ Var B B @ Var B A @ OB'] oo [Var A B @ OA' @ Var B B @ Var B A @ OB' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ Var B A @ I \<leadsto> Var B B @ Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ((fb ^^ length (Var B B)) (ID (TVs (Var B B)) \<parallel> [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B B @ Var B A @ OB' @ Var A B @ OA' \<leadsto> Var B B @ Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo ([Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA']) oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'])) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo [Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo (fb ^^ length (Var B B)) (([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'])) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) \<parallel> (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'])) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo ([Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA']) oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo [Var A B @ IB' @ Var B A @ IA' \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O'])))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo ([Var A B @ OA' @ Var B A @ OB' \<leadsto> Var B A @ OB' @ Var A B @ OA'] oo [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var A B @ Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo ID (TVs (Var A B)) \<parallel> [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [Var A B @ OA' @ Var B A @ OB' \<leadsto> Var A B @ Var B A @ O'])) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo ID (TVs (Var A B)) \<parallel> [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) ([Var A B @ Var B A @ I \<leadsto> Var B A @ IA' @ Var A B @ IB'] oo (fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']) \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> (fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo ([OA'' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo ID (TVs OA') \<parallel> Trs (FB B) oo ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo ([OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo ID (TVs OA') \<parallel> Trs (FB B) oo ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo ([OA'' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo ID (TVs OA') \<parallel> Trs (FB B) oo ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo [OA' @ OB'' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo [OA' @ OB'' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A ;; FB B) oo [OA' @ OB'' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo (ID (TVs OA') \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo [OA' @ OB'' \<leadsto> OA' @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ([OA' @ Var A B @ IB' \<leadsto> OA' @ IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo [OA' @ OB'' \<leadsto> OA' @ Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo ([OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo [OA' @ Var A B @ IB' \<leadsto> OA' @ IB'']) oo ID (TVs OA') \<parallel> Trs (FB B) oo ([OA' @ OB'' \<leadsto> OA' @ Var B A @ OB'] oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']))\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo (ID (TVs OA') \<parallel> [Var A B @ IB' \<leadsto> IB''] oo ID (TVs OA') \<parallel> Trs (FB B) oo ID (TVs OA') \<parallel> [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' @ IB' \<leadsto> Var A B @ OA' @ IB'] oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>(fb ^^ length (Var B A)) ([Var B A @ IA' \<leadsto> IA''] \<parallel> ID (TVs IB') oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O']) = (fb ^^ length (Var B A)) ([Var B A @ IA' @ IB' \<leadsto> IA'' @ IB'] oo Trs (FB A) \<parallel> ID (TVs IB') oo [OA'' \<leadsto> Var A B @ OA'] \<parallel> ID (TVs IB') oo [Var A B @ OA' @ IB' \<leadsto> OA' @ Var A B @ IB'] oo ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo [OB'' \<leadsto> Var B A @ OB']) oo [OA' @ Var B A @ OB' \<leadsto> Var B A @ O'])\<close> \<open>FB (A ||| B) = \<lparr>In = I, Out = O', Trs = (fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'])\<rparr>\<close> \<open>In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B) = IA' @ IB'\<close> \<open>Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B) = O'\<close> by presburger
            then show ?thesis
              by (metis FB_def)
          qed
    qed



    definition VarSwitch :: "'var list \<Rightarrow> 'var list \<Rightarrow> ('var, 'a) Dgr" ("[[_ \<leadsto> _]]") where
      "VarSwitch x y = \<lparr>In = x, Out = y, Trs = [x \<leadsto> y]\<rparr>"
      

      definition "in_equiv  A B = (perm (In A) (In B) \<and> Trs A = [In A \<leadsto> In B] oo Trs B \<and> Out A  = Out B)"
      definition "out_equiv A B = (perm (Out A) (Out B) \<and> Trs A = Trs B oo [Out B \<leadsto> Out A] \<and> In A = In B)"

      definition "in_out_equiv A B = (perm (In A) (In B) \<and> perm (Out A) (Out B) \<and> Trs A = [In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A])"

      lemma in_equiv_type_ok[simp]: "in_equiv A B \<Longrightarrow> type_ok B \<Longrightarrow> type_ok A"
        apply (simp add: type_ok_def in_equiv_def, safe)
        using dist_perm perm_sym by blast

      lemma in_equiv_sym: "type_ok B \<Longrightarrow> in_equiv A B \<Longrightarrow> in_equiv B A"
        by (auto simp add: in_equiv_def perm_sym  comp_assoc[THEN sym] type_ok_def switch_comp perm_set_eq)
      
      lemma in_equiv_eq: "type_ok A \<Longrightarrow> A = B \<Longrightarrow> in_equiv A B"
        by (simp add: in_equiv_def perm_def type_ok_def)

      lemma [simp]: "type_ok A \<Longrightarrow> [In A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Out A] = Trs A"
        by (simp add: type_ok_def)

      lemma in_equiv_tran: "type_ok C \<Longrightarrow> in_equiv A B \<Longrightarrow> in_equiv B C \<Longrightarrow> in_equiv A C"
        apply (subgoal_tac "type_ok B")
        apply (subgoal_tac "type_ok A")
        apply (simp add: in_equiv_def)
        apply simp_all
        apply (cut_tac x="In A" and y="In B" and z="In C" in  perm_trans)
        apply simp_all
        apply (subst comp_assoc [THEN sym])
        apply simp_all
        apply (unfold type_ok_def, simp_all)
        apply (subst switch_comp, simp_all)
        using perm_set_eq by auto

    lemma in_out_equiv_refl: "type_ok A \<Longrightarrow> in_out_equiv A A"
      by (simp add: in_out_equiv_def perm_def)

    lemma in_out_equiv_sym: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> in_out_equiv A B \<Longrightarrow> in_out_equiv B A"
      apply (simp add: in_out_equiv_def, safe)
      apply (simp add: perm_def)
      apply (simp add: perm_def)
      apply (simp add: type_ok_def)
      apply (simp add: comp_assoc)
      apply (subgoal_tac "[Out B \<leadsto> Out A] oo [Out A \<leadsto> Out B] = ID (TVs (Out B))")
      apply simp_all
      apply (simp add: comp_assoc [THEN sym])
      apply (subgoal_tac "[In B \<leadsto> In A] oo [In A \<leadsto> In B] =  ID (TVs (In B))")
      apply simp_all
      apply (simp add: distinct_vars_comp perm_sym)
      by (simp add: distinct_vars_comp perm_sym)

    lemma in_out_equiv_tran: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> in_out_equiv A B \<Longrightarrow> in_out_equiv B C \<Longrightarrow> in_out_equiv A C"
      apply (simp add: in_out_equiv_def, safe)
      apply (simp add: perm_def)
      apply (simp add: perm_def)
      apply (unfold type_ok_def, safe)
      proof -
        assume [simp]: "TVs (In A) = TI (Trs A)" 
        assume [simp]: "TVs (In B) = TI (Trs B) "
        assume [simp]: "TVs (In C) = TI (Trs C) "
        assume [simp]: "TVs (Out A) = TO (Trs A) "
        assume [simp]: "TVs (Out B) = TO (Trs B) "
        assume [simp]: "TVs (Out C) = TO (Trs C) "
        have [simp]: "[In A \<leadsto> In B] oo ([In B \<leadsto> In C] oo Trs C oo [Out C \<leadsto> Out B]) oo [Out B \<leadsto> Out A]
          = ([In A \<leadsto> In B] oo [In B \<leadsto> In C]) oo Trs C oo ([Out C \<leadsto> Out B] oo [Out B \<leadsto> Out A])"
          by (simp add: comp_assoc)
        assume [simp]: "perm (In A) (In B)"
        assume "perm (In B) (In C)"
        assume "perm (Out A) (Out B)"
        assume "perm (Out B) (Out C)"
        assume [simp]: "distinct (In A)"
        assume [simp]: "distinct (Out C)"

        have [simp]: "[In A \<leadsto> In B] oo [In B \<leadsto> In C] = [In A \<leadsto> In C]"
          apply (subst  switch_comp, simp_all)
          using \<open>perm (In B) (In C)\<close> perm_set_eq by auto

        have [simp]: "[Out C \<leadsto> Out B] oo [Out B \<leadsto> Out A] = [Out C \<leadsto> Out A]"
          apply (subst  switch_comp, simp_all)
          apply (simp add: \<open>perm (Out B) (Out C)\<close> perm_sym)
          using \<open>perm (Out A) (Out B)\<close> perm_set_eq by auto
        show " [In A \<leadsto> In B] oo ([In B \<leadsto> In C] oo Trs C oo [Out C \<leadsto> Out B]) oo [Out B \<leadsto> Out A] = [In A \<leadsto> In C] oo Trs C oo [Out C \<leadsto> Out A]"
          by simp
     qed



    lemma [simp]: "set x \<inter> set (y \<ominus> x) = {}"
      by (simp add: set_diff)

    declare distinct_diff [simp]

    lemma [simp]: "distinct (Out A) \<Longrightarrow> distinct (Var A B)"
      by (simp add: Var_def distinct_inter)

    lemma [simp]: "set (Var A B) \<subseteq> set (Out A)"
      by (auto simp add: Var_def set_inter)
    lemma [simp]: "set (Var A B) \<subseteq> set (In B)"
      by (auto simp add: Var_def set_inter)


    lemma [simp]:" distinct x \<Longrightarrow> distinct y \<Longrightarrow> set x \<subseteq> set y \<Longrightarrow> perm (x @ (y \<ominus> x)) y"
      using diff_subset perm_switch by fastforce

    declare perm_set_eq [simp]

    lemma [simp]: "perm x y \<Longrightarrow> set x \<subseteq> set y"
      by simp
    lemma [simp]: "perm x y \<Longrightarrow> set y \<subseteq> set x"
      by simp

    lemma [simp]: "set (x \<ominus> y) \<subseteq> set x"
      by (auto simp add: set_diff)

    lemmas fb_indep_sym = fb_indep [THEN sym]

    declare length_TVs [simp]      

    lemmas fb_perm_sym = fb_perm [THEN sym]

      lemma perm_diff[simp]: "\<And> x' . perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x \<ominus> y) (x' \<ominus> y')"
        apply (induction x, simp_all)
        apply (frule_tac x = y and y = y' in perm_set_eq, simp)
        apply (simp add: split_perm union_diff)
        apply auto
        apply (simp_all add: union_diff)
        apply (metis union_diff)
        by (metis union_diff)

    lemma [simp]: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x @ y) (x' @ y')"
      by (simp add: perm_def)

    lemma [simp]: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x \<oplus> y) (x' \<oplus> y')"
      by (simp add: addvars_def)

    term "(ya @ a # y'a) \<otimes> y'"

    lemma [simp]: "\<And> x' . perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x \<otimes> y) (x' \<otimes> y')"
      apply (induction x, simp_all, safe)
      apply (simp add: split_perm, safe, simp_all)
      apply (rule_tac x = "ya \<otimes> y'" in exI)
      apply (rule_tac x = "y'a \<otimes> y'" in exI)
      apply (simp add: append_inter)
      apply (subgoal_tac "perm (x \<otimes> y) ((ya @ y'a) \<otimes> y')")
      apply (subst (asm) append_inter, simp_all)

      apply (simp add: split_perm, safe, simp_all)
      apply (subgoal_tac "perm (x \<otimes> y) ((ya @ y'a) \<otimes> y')")
      apply (subst (asm) append_inter, simp add: append_inter)
      by simp

    declare distinct_inter [simp]

    lemma perm_ops: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      apply safe
      by (simp_all)
      

    lemma [simp]: "perm x' x \<Longrightarrow> perm y' y \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      by (rule_tac x = x and y = y and x' = x' and y' = y' in perm_ops, unfold perm_def, simp_all)
      
    lemma [simp]: "perm x x' \<Longrightarrow> perm y' y \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      by (rule_tac x = x and y = y and x' = x' and y' = y' in perm_ops, unfold perm_def, simp_all)

    lemma [simp]: "perm x' x \<Longrightarrow> perm y y' \<Longrightarrow> f = op \<otimes> \<or> f = op \<ominus> \<or> f = op \<oplus> \<Longrightarrow> perm (f x y) (f x' y')"
      by (rule_tac x = x and y = y and x' = x' and y' = y' in perm_ops, unfold perm_def, simp_all)

    

    lemma in_out_equiv_FB: "type_ok B \<Longrightarrow> in_out_equiv A B \<Longrightarrow> in_out_equiv (FB A) (FB B)"
      proof -
        assume A: "type_ok B"
        assume B: "in_out_equiv A B"
        have [simp]: "length (Var A A) = length (Var B B)"
          using A B by (simp add: type_ok_def in_out_equiv_def Var_def perm_length)
        have [simp]: "TI (Trs B) = TVs (In B)" and [simp]: "TO (Trs B) = TVs (Out B)" and [simp]: "distinct (In A)" and [simp]: "distinct (Out A)" 
          and [simp]: "distinct (Out B)" and [simp]: "perm (Out B) (Out A)"
          using A B apply (simp_all add: type_ok_def in_out_equiv_def Var_def perm_sym)
          using dist_perm perm_sym apply blast
          using dist_perm perm_sym by blast
        have [simp]: "perm (Var A A) (Var B B)"
          apply (simp add: Var_def)
          using B in_out_equiv_def perm_ops by blast
        have [simp]: "set (Var B B) \<inter> set (In A \<ominus> Var A A) = {}"
          by (metis Var_def \<open>distinct (In A)\<close> \<open>distinct (Out A)\<close> \<open>perm (Var A A) (Var B B)\<close> addvars_def distinct_addvars distinct_append distinct_inter perm_set_eq)
        have [simp]: "set (In B \<ominus> Var B B) \<subseteq> set (In A \<ominus> Var A A)"
          by (metis (full_types) B \<open>perm (Var A A) (Var B B)\<close> in_out_equiv_def order_refl perm_diff perm_set_eq)
        have [simp]: " perm (Var B B @ (In A \<ominus> Var A A)) (Var B B @ (In B \<ominus> Var B B))"
          using B \<open>perm (Var A A) (Var B B)\<close> in_out_equiv_def perm_diff perm_union_right by blast
        have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> set (In B \<ominus> Var B B)"
          by (simp add: set_diff)
          
        have [simp]: "set (Out A \<ominus> Var A A) \<subseteq> set (Out B \<ominus> Var B B)"
          by auto
        have [simp]: "perm (Out B) (Var B B @ (Out B \<ominus> Var B B))"
          by (metis A Var_def diff_inter_left perm_switch_aux_c perm_sym type_ok_def)
        have [simp]: " set (Out A \<ominus> Var A A) \<subseteq> set (Var B B) \<union> set (Out B \<ominus> Var B B)"
          using \<open>set (Out A \<ominus> Var A A) \<subseteq> set (Out B \<ominus> Var B B)\<close> by blast
        have [simp]: "perm (Var A A @ (In A \<ominus> Var A A)) (Var B B @ (In A \<ominus> Var A A))"
          using \<open>perm (Var A A) (Var B B)\<close> perm_union_left by blast
        have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> set (In A \<ominus> Var A A)"
          using \<open>set (In B \<ominus> Var B B) \<subseteq> set (In A \<ominus> Var A A)\<close> \<open>set (In B) \<subseteq> set (Var B B) \<union> set (In B \<ominus> Var B B)\<close> by blast
        have [simp]: "perm (Out B) (Var B B @ (Out A \<ominus> Var A A))"
          by (meson \<open>perm (Out B) (Out A)\<close> \<open>perm (Out B) (Var B B @ (Out B \<ominus> Var B B))\<close> \<open>perm (Var A A) (Var B B)\<close> perm_diff perm_sym perm_trans perm_union_right)
        have [simp]: "set (Var A A) \<subseteq> set (Var B B) \<union> set (Out A \<ominus> Var A A)"
          using perm_set_eq by force

        have C: "ID (TVs (Var B B)) \<parallel> [In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo [Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] =  [Var B B @ (In A \<ominus> Var A A) \<leadsto> In B]"
          by (subst distinct_id [THEN sym], simp_all add: par_switch switch_comp)
        have D: "[Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)] oo ID (TVs (Var B B)) \<parallel> [Out B \<ominus> Var B B \<leadsto> Out A \<ominus> Var A A] = [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)]"
          by (subst distinct_id [THEN sym], simp_all add: par_switch switch_comp)
        have E: "[Var A A @ (In A \<ominus> Var A A) \<leadsto> Var B B @ (In A \<ominus> Var A A)] oo [Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] = [Var A A @ (In A \<ominus> Var A A) \<leadsto> In B]"
          by (subst switch_comp, simp_all)
        have F: "[Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)] oo [Var B B @ (Out A \<ominus> Var A A) \<leadsto> Var A A @ (Out A \<ominus> Var A A)] =  [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)]"
          by (subst switch_comp, simp_all)
        have "[In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo (fb ^^ length (Var B B)) ([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo (Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])) oo [Out B \<ominus> Var B B \<leadsto> Out A \<ominus> Var A A]
          = (fb ^^ length (Var B B))
            ((ID (TVs (Var B B)) \<parallel> [In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo [Var B B @ (In B \<ominus> Var B B) \<leadsto> In B]) oo Trs B 
            oo ([Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)] oo ID (TVs (Var B B)) \<parallel> [Out B \<ominus> Var B B \<leadsto> Out A \<ominus> Var A A]))"
          apply (subst fb_indep_a [THEN sym])
          apply (simp_all add: fbtype_def, simp)
          by (simp add: comp_assoc)
      also have "... = (fb ^^ length (Var B B)) ([Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)])"
        by (simp add: C D)
      thm fb_perm
      also have "... = (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
          apply (subst fb_perm_sym [of "Var B B" "Var A A" "In A \<ominus> Var A A" "Out A \<ominus> Var A A"])
          using A B apply (auto simp add: Var_def fbtype_def in_out_equiv_def type_ok_def set_inter set_diff) [4]
          by (simp add: comp_assoc_middle_ext E F)
      also from B have "... = (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo ([In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]) oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
          apply (simp add: comp_assoc [THEN sym] switch_comp in_out_equiv_def)
          by (simp add: comp_assoc switch_comp)

      finally show ?thesis
        using A B apply (simp add: FB_def in_out_equiv_def Let_def)
        by (simp add: comp_assoc [THEN sym] switch_comp)
      qed

(*the theorem FB_in_out_equiv and Parallel_in_out_equiv replaces next*)
        
  end


  primrec op_list :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow>'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
    "op_list e opr [] = e" |
    "op_list e opr (a # x) = opr a (op_list e opr x)"

     primrec inter_set :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" where
      "inter_set [] X = []" |
      "inter_set (x # xs) X = (if x \<in> X then x # inter_set xs X else inter_set xs X)"

     lemma list_inter_set: "x \<otimes> y = inter_set x (set y)"
      by (induction x, simp_all)


  context BaseOperationVars 
    begin
      definition ParallelId :: "('var, 'a) Dgr" ("\<box>")
        where "\<box> =  \<lparr>In = [], Out = [], Trs = ID []\<rparr>" 

      lemma ParallelId_right[simp]: "type_ok A \<Longrightarrow> A ||| \<box> = A"
        apply (simp add: Parallel_def ParallelId_def)
        apply (subst comp_id_switch)
        apply (simp add: type_ok_def)
        apply (simp add: type_ok_def)
        apply (cut_tac x="[]" in  distinct_id)
        apply simp
        apply (subgoal_tac "TVs [] = []")
        using par_empty_right apply auto[1]
        by (simp add: TVs_def)

      lemma ParallelId_left: "type_ok A \<Longrightarrow> \<box> ||| A = A"
        apply (simp add: Parallel_def ParallelId_def)
        apply (subst comp_id_switch)
        by (simp_all add: type_ok_def)


      definition "parallel_list = op_list (ID []) (op \<parallel>)"
      definition "Parallel_list = op_list \<box> (op |||)"





      (*not used deterministic \<Longrightarrow> decomposable*)
      definition "decomposable A As = (in_equiv A (Parallel_list As)
            \<and> type_ok A
            \<and> (\<forall> B \<in> set As . type_ok B)
            \<and> ((\<forall> B \<in> set As . length (Out B) = 1) \<or> (length As = 1 \<and> Out (hd As) = [])))" (*As has on component for all outputs of A or if A has empty output, then As has one element with empty output *)

      definition "io_rel A = set (Out A) \<times> set (In A)"

      definition "IO_Rel As = \<Union> (set (map io_rel As))"


      definition "out A = hd (Out A)" (*the first output of A*)

      definition "Type_OK As = ((\<forall> B \<in> set As . type_ok B \<and> length (Out B) = 1) 
                    \<and> distinct (concat (map Out As)))"

      lemma concat_map_out: "(\<forall> A \<in> set As . length (Out A) = 1) \<Longrightarrow> concat (map Out As) = map out As"
        apply (induction As, simp_all)
        apply (case_tac "Out a", simp_all)
        by (simp add: out_def)

      lemma Type_OK_simp: "Type_OK As =  ((\<forall> B \<in> set As . type_ok B \<and> length (Out B) = 1) \<and> distinct (map out As))"
        apply (simp add: Type_OK_def, safe)
        by (simp_all add: concat_map_out)

      definition "single_out A = (type_ok A \<and> length (Out A) = 1)"


      definition "CompA A B = (if out A \<in> set (In B) then A ;; B else B)"
 
      definition "internal As = {x . (\<exists> A \<in> set As . \<exists> B \<in> set As . x = out A \<and> out A \<in> set (In B))}"


      primrec get_comp_out :: "'c \<Rightarrow> ('c, 'd) Dgr list \<Rightarrow> ('c, 'd) Dgr" where
        "get_comp_out x (A # As) = (if out A = x then A else get_comp_out x As)"

      primrec get_other_out :: "'c \<Rightarrow> ('c, 'd) Dgr list \<Rightarrow> ('c, 'd) Dgr list" where
        "get_other_out x [] = []" |
        "get_other_out x (A # As) = (if out A = x then get_other_out x As else A # get_other_out x As)"
    
      (*we assume the A is not in As*)
      definition "fb_less_step A As = map (CompA A) As"

      (*we assume the A is not in As*)
      definition "fb_out_less_step x As = fb_less_step (get_comp_out x As) (get_other_out x As)"

      primrec fb_less :: "'var list \<Rightarrow> ('var, 'a) Dgr list \<Rightarrow> ('var, 'a) Dgr list" where
        "fb_less [] As = As" |
        "fb_less (x # xs) As = fb_less xs (fb_out_less_step x As)"

      definition "FB_Var A = Var A A"

      definition "loop_free As = (\<forall> x . (x,x) \<notin> (IO_Rel As)\<^sup>+)"

      lemma [simp]: "Parallel_list (A # As) = (A ||| Parallel_list As)"
        by (simp add: Parallel_list_def)

      lemma [simp]: "Out (A ||| B) = Out A @ Out B"
        by (simp add: Parallel_def)

      lemma [simp]: "In (A ||| B) = In A \<oplus> In B"
        by (simp add: Parallel_def)

      lemma Type_OK_cons: "Type_OK (A # As) = (type_ok A \<and> length (Out A) = 1 \<and> set (Out A) \<inter> (\<Union>a\<in>set As. set (Out a)) = {} \<and> Type_OK As)"
        by (simp add: Type_OK_def type_ok_def, auto)

      lemma [simp]: "Out \<box> = []"
        by (simp add: ParallelId_def)
    
      lemma Out_Parallel: "Out (Parallel_list As) = concat (map Out As)"
        apply (induction As)
        apply auto
        by (simp add: Parallel_list_def)

      lemma "FB_Var (A ||| B) = Out A @ Out B \<otimes> (In A \<oplus> In B)"
        by (simp add: FB_Var_def Parallel_def Var_def)
    

      lemma internal_cons: "internal (A # As) = {x. x = out A \<and> (out A \<in> set (In A) \<or> (\<exists>B\<in>set As. out A \<in> set (In B)))} \<union> {x . (\<exists>Aa\<in>set As. x = out Aa \<and> (out Aa \<in> set (In A)))}
          \<union> internal As"
        by (auto simp add: internal_def)
     
      lemma Out_out: "length (Out A) = Suc 0 \<Longrightarrow> Out A = [out A]"
        apply (simp add: out_def)
        by (case_tac "Out A", simp_all)

      lemma Type_OK_out: "Type_OK As \<Longrightarrow> A \<in> set As  \<Longrightarrow> Out A = [out A]"
        apply (simp add: out_def Type_OK_def)
        by (case_tac "Out A", simp_all, auto)


      lemma [simp]: "Parallel_list [] = \<box>"
        by (simp add: Parallel_list_def)

      lemma [simp]: "In \<box> = []"
        by (simp add: ParallelId_def)

      lemma In_Parallel: "In (Parallel_list As) = op_list [] (op \<oplus>) (map In As)"
        by (induction As, simp_all)

      lemma [simp]: "set (op_list [] op \<oplus> xs) = \<Union> set (map set xs)"
        apply (induction xs, simp_all)
        by (simp add: set_addvars)

      lemma internal_FB_Var: "Type_OK As \<Longrightarrow> internal As = set (FB_Var (Parallel_list As))"
        apply (induction As)
        apply (simp add: FB_Var_def Var_def internal_def Parallel_list_def ParallelId_def)
        apply (subgoal_tac "Out a = [out a]")
        apply (simp add: Type_OK_cons FB_Var_def Var_def set_inter set_addvars internal_cons Type_OK_out Out_Parallel, safe)
        apply (simp_all add: Type_OK_out)
        apply (rule_tac x = Aa in bexI)
        apply (simp add: Type_OK_out, simp)
        apply (rule_tac x = xa in bexI)
        apply (simp add: Type_OK_out, simp)
        apply blast
        apply blast
        apply blast
        apply auto
        apply (simp add: In_Parallel)
        apply (simp add: In_Parallel)
        by (simp add: In_Parallel)


      lemma map_Out_fb_less_step: "length (Out A) = 1 \<Longrightarrow>  map Out (fb_less_step A As) = map Out As"
        apply (induction As)
        apply (simp_all add: fb_less_step_def CompA_def Comp_def Let_def Var_def diff_inter_left, safe)
        by (case_tac "Out A", simp_all add: out_def)

      lemma mem_get_comp_out: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> get_comp_out (out A) As = A"
        apply (induction As, simp, auto)
        apply (simp add: Type_OK_def, auto)
        apply (simp add: set_eq_iff)
        apply (drule_tac x = "out a" in spec, safe)
        apply (case_tac "Out a")
        apply (simp_all add: out_def)
        apply (drule_tac x = A in bspec, simp)
        apply (drule_tac x = A in bspec, simp_all, safe)
        apply (case_tac "Out A")
        apply (simp_all)
        by (simp add: Type_OK_cons)
 
      lemma map_Out_fb_out_less_step: "A \<in> set As \<Longrightarrow> Type_OK As \<Longrightarrow> a = out A \<Longrightarrow> map Out (fb_out_less_step a As) = map Out (get_other_out a As)"
        apply (induction As, simp add: fb_out_less_step_def fb_less_step_def)
        apply simp
        apply safe
        apply (simp add: fb_out_less_step_def)
        apply (subst map_Out_fb_less_step)
        apply (simp add: Type_OK_def)
        apply simp
        apply (simp add: fb_out_less_step_def)
        apply (subst map_Out_fb_less_step, simp_all)
        apply (simp add: Type_OK_def)
        apply (simp add: fb_out_less_step_def)
        apply (subst map_Out_fb_less_step, simp_all)
        apply (subst mem_get_comp_out, simp_all)
        apply (simp add: Type_OK_cons)
        by (simp add: Type_OK_def)

      lemma [simp]: "Type_OK (A # As) \<Longrightarrow> Type_OK As"
        by (simp add: Type_OK_cons)

      lemma Type_OK_Out: "Type_OK (A # As) \<Longrightarrow> Out A = [out A]"
        by (rule Type_OK_out, simp_all, auto)

      lemma  concat_map_Out_get_other_out: "Type_OK As \<Longrightarrow> concat (map Out (get_other_out a As)) = (concat (map Out As) \<ominus> [a])"
        apply (induction As, simp_all)
        by (simp_all add: union_diff Type_OK_Out)
      
      lemma FB_Var_cons_out: "Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = a # L \<Longrightarrow> \<exists> A \<in> set As . out A = a"
        apply (cut_tac As = As in internal_FB_Var, simp_all)
        apply (simp add: internal_def set_eq_iff)
        by (drule_tac x = a in spec, simp_all, safe, blast)


      lemma FB_Var_cons_out_In: "Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = a # L \<Longrightarrow> \<exists> B \<in> set As . a \<in> set (In B)"
        apply (cut_tac As = As in internal_FB_Var, simp_all)
        apply (simp add: internal_def set_eq_iff)
        by (drule_tac x = a in spec, simp_all, safe)


      (*todo: find better names to next lemmas*)
      lemma AAA_a: "Type_OK (A # As) \<Longrightarrow> A \<notin> set As"
        apply (simp add: Type_OK_def, auto)
        by (case_tac "Out A", simp_all, auto)

      lemma AAA_c: "a \<notin> set x \<Longrightarrow> x \<ominus> [a] = x"
        by (induction x, simp_all, auto)

      lemma AAA_b: "(\<forall> A \<in> set As. a \<noteq> out A) \<Longrightarrow> get_other_out a As = As"
        by (induction As, simp_all, auto)

     
      lemma AAA_d: "Type_OK (A # As) \<Longrightarrow> \<forall>Aa\<in>set As. out A \<noteq> out Aa"
        apply (simp add: Type_OK_def)
        apply (simp add: set_eq_iff)
        apply (case_tac "Out A", simp_all, safe)
        apply (drule_tac x = "a" in spec, safe, auto)
        apply (drule_tac x = Aa in bspec, simp_all)
        apply (drule_tac x = Aa in bspec, simp_all)
        apply (case_tac "Out Aa", simp_all, auto)
        apply (simp add: out_def)
        apply (drule_tac x = Aa in bspec, simp_all)
        apply (drule_tac x = Aa in bspec, simp_all)
        apply (case_tac "Out Aa", simp_all, auto)
        by (simp add: out_def)

      lemma  mem_get_other_out: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> get_other_out (out A) As = (As \<ominus> [A])"
        apply (induction As)
        apply simp
        apply simp
        apply safe   
        apply simp_all
        apply (subst AAA_c)
        apply (subst AAA_a, simp_all)
        apply (subst AAA_b, simp_all)
        apply (rule AAA_d, simp_all)
        using AAA_d by blast

      lemma In_CompA: "In (CompA A B) = (if out A \<in> set (In B) then In A \<oplus> (In B \<ominus> Out A) else In B)"
        apply (simp add: CompA_def, safe)
        by (simp add: Comp_def Let_def Var_def diff_inter_right)
       

      lemma union_set_In_CompA: "length (Out A) = 1 \<Longrightarrow> B \<in> set As \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> (\<Union>x\<in>set As. set (In (CompA A x))) = set (In A) \<union> ((\<Union> B \<in> set As . set (In B)) - {out A})"
        apply (induction As, simp_all)
        apply auto
        apply (simp add: In_CompA set_addvars set_diff)
        apply (case_tac "out A \<in> set (In a)")
        apply (simp add: In_CompA set_addvars set_diff)
        apply (simp add: In_CompA set_addvars set_diff)
        apply (case_tac "out A \<in> set (In xa)")
        apply (simp add: In_CompA set_addvars set_diff)
        apply (simp add: In_CompA set_addvars set_diff)
        apply (simp add: In_CompA set_addvars set_diff)
        apply (simp_all add: Out_out)
        apply (case_tac "out A \<in> set (In a)")
        apply (simp_all add: In_CompA set_addvars set_diff Out_out)
        apply (case_tac " out A \<in> set (In xa)")
        apply (simp_all add: In_CompA set_addvars set_diff Out_out)
        apply (case_tac " out A \<in> set (In a)")
        apply (simp_all add: In_CompA set_addvars set_diff Out_out)
        apply auto
        apply (drule_tac x = xa in bspec, simp_all)
        apply (case_tac "out A \<in> set (In xa)")
        by (simp_all add: In_CompA set_addvars set_diff Out_out)
      

      lemma BBBB_a: "inter_set (x \<ominus> [a]) (X \<union> ((\<Union>x\<in>Z. set (In x)) - {a})) = inter_set (x \<ominus> [a]) (X \<union> ((\<Union>x\<in>Z. set (In x))))"
        by (induction x, simp_all)

      lemma BBBB_b: "A \<in> set As \<Longrightarrow> (set (In A) \<union> (\<Union>x\<in>set As - {A}. set (In x))) = ((\<Union>x\<in>set As. set (In x)))"
        by (induction As, simp_all, auto)


      lemma BBBB_c:"\<And> L . a \<notin> set L \<Longrightarrow> inter_set x X = L \<Longrightarrow> a \<in> X \<Longrightarrow> inter_set (x \<ominus> [a]) X = L"
        by (induction x, simp_all, auto)

      lemma BBBB_d: "\<And> L . a \<notin> set L \<Longrightarrow>  inter_set x X = a # L \<Longrightarrow> inter_set (x \<ominus> [a]) X = L"
        apply (induction x, simp_all, safe, simp_all)
        by (rule BBBB_c, simp_all)

      lemma BBBB_e: "Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = out A # L \<Longrightarrow> A \<in> set As \<Longrightarrow> out A \<notin> set L"
        apply (simp add: FB_Var_def Var_def Out_Parallel Type_OK_def, safe)
        by (drule_tac y = "In (Parallel_list As)" in distinct_inter, simp)

      lemma BBBB_f: "loop_free As \<Longrightarrow>
           Type_OK As \<Longrightarrow> A \<in> set As  \<Longrightarrow> B \<in> set As \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> B \<noteq> A"
        apply (simp add: loop_free_def)
        apply (drule_tac x = "out A" in spec)
        apply (simp add: IO_Rel_def io_rel_def)
        apply (case_tac "B = A", simp_all)
          apply (simp add: io_rel_def)
          apply (subgoal_tac "(out A, out A) \<in> (\<Union>x\<in>set As. set (Out x) \<times> set (In x))\<^sup>+", simp)
          
        apply (rule r_into_trancl')
        apply simp
        apply (rule_tac x = A in bexI)
        by (simp_all add: Type_OK_out)
          
      thm union_set_In_CompA
        
        term SUPREMUM

      lemma FB_Var_fb_out_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = a # L \<Longrightarrow> FB_Var (Parallel_list (fb_out_less_step a As)) = L"
        apply (frule FB_Var_cons_out, simp_all, safe)
        apply (frule FB_Var_cons_out_In, simp_all, safe)
        apply (frule BBBB_e, simp_all)
        apply (simp add: FB_Var_def Var_def Out_Parallel In_Parallel)
        apply (subst map_Out_fb_out_less_step, simp_all)
        apply (subst concat_map_Out_get_other_out, simp)
        apply (simp add: fb_out_less_step_def mem_get_comp_out mem_get_other_out fb_less_step_def)
        apply (simp add: list_inter_set)
        apply (subgoal_tac "(UNION (set (As \<ominus> [A])) (set \<circ> (In \<circ> CompA A))) = (\<Union>x\<in>set (As \<ominus> [A]). set (In (CompA A x)))")
          apply simp
        apply (subst union_set_In_CompA, simp_all)
        apply (simp add: Type_OK_def)
        apply (simp add: set_diff)
        thm BBBB_f
        apply (rule BBBB_f, simp_all)
        apply (simp add: set_diff BBBB_a BBBB_b)
        apply (rule BBBB_d)
        by simp_all

      lemma distinct_perm_set_eq: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm x y = (set x = set y)"
        using perm_def set_eq_iff_mset_eq_distinct by blast

      lemma set_perm: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set x = set y \<Longrightarrow> perm x y"
        by (simp add: distinct_perm_set_eq)

      lemma Parallel_list_cons:"Parallel_list (a # As) = a ||| Parallel_list As"
        by simp

      lemma type_ok_parallel_list: "Type_OK As \<Longrightarrow> type_ok (Parallel_list As)"
        apply (induction As)
        apply (simp add: ParallelId_def type_ok_def)
        apply (simp only: Parallel_list_cons)
        apply (subst type_ok_Parallel)
        by (simp_all add: Type_OK_def Out_Parallel)

      lemma BBB_a: "length (Out A) = 1 \<Longrightarrow> Out (CompA A B) = Out B"
        apply (simp add: CompA_def, safe)
        apply (simp add: Comp_def Let_def Var_def diff_inter_left out_def)
        by (case_tac "Out A", simp_all)

      lemma BBB_b: "length (Out A) = 1 \<Longrightarrow> map (Out \<circ> CompA A) As = map Out As"
        apply (induction As, simp_all)
        by (simp add: BBB_a)

      lemma BBB_c: "distinct (map f As) \<Longrightarrow> distinct (map f (As \<ominus> Bs))"
        by (induction As, simp_all add: image_def set_diff)

      lemma type_ok_CompA: "type_ok A \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> type_ok B \<Longrightarrow> type_ok (CompA A B)"
        apply (simp add: CompA_def, safe)
        apply (subst Comp_in_out)
        apply simp_all
        using Out_out apply fastforce
        by (simp add: Let_def Var_def diff_inter_left diff_inter_right type_ok_def addvars_def set_diff)


      lemma Type_OK_fb_out_less_step_aux: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow>  Type_OK (fb_less_step A (As \<ominus> [A]))"
        apply (unfold fb_less_step_def)
        apply (subst Type_OK_def, safe, simp_all add: image_def, safe)
        apply (subst type_ok_CompA, simp_all)
        apply (simp add: Type_OK_def)
        apply (simp add: Type_OK_def)
        apply (simp add: Type_OK_def set_diff)
        apply (subst BBB_a)
        apply (simp add: Type_OK_def)
        apply (simp add: Type_OK_def set_diff)
        apply (subst BBB_b)
        apply (simp add: Type_OK_def)
        apply (subst concat_map_out)
        apply (simp add: Type_OK_def set_diff)
        by (simp add: Type_OK_simp BBB_c)

    
      theorem Type_OK_fb_out_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow>
        FB_Var (Parallel_list As) = a # L \<Longrightarrow> Bs = fb_out_less_step a As \<Longrightarrow> Type_OK Bs"
        apply (frule FB_Var_cons_out, simp_all, safe)
        (*apply (frule FB_Var_cons_out_In, simp_all, safe)*)
        apply (simp add: fb_out_less_step_def)
        apply (subgoal_tac "(get_comp_out (out A) As) = A", simp_all)
        apply (subgoal_tac "get_other_out (out A) As = (As \<ominus> [A])", simp_all)
        apply (rule Type_OK_fb_out_less_step_aux, simp_all)
        using mem_get_other_out apply blast
        using mem_get_comp_out by blast


      lemma Type_OK_loop_free_elem: "Type_OK As \<Longrightarrow> loop_free As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A \<notin> set (In A)"
        apply (simp add: loop_free_def)
        apply (drule_tac x = "out A" in spec)
        apply (simp add: IO_Rel_def io_rel_def)
        apply (case_tac "out A \<in> set (In A)", simp_all)
          apply (simp add: io_rel_def)
        apply (drule_tac P =  "(out A, out A) \<in> (\<Union>x\<in>set As. set (Out x) \<times> set (In x))\<^sup>+" in notE, simp_all)
        apply (rule r_into_trancl')
        apply simp
        apply (rule_tac x = A in bexI)
        by (simp_all add: Type_OK_out)


      lemma perm_FB_Parallel[simp]: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow>
            FB_Var (Parallel_list As) = a # L \<Longrightarrow> Bs = fb_out_less_step a As 
             \<Longrightarrow> perm (In (FB (Parallel_list As))) (In (FB (Parallel_list Bs)))"
        apply (frule FB_Var_cons_out, simp_all, safe)
        apply (frule FB_Var_cons_out_In, simp_all, safe)
        apply (rule set_perm)
        apply (drule type_ok_parallel_list)
        apply (drule Type_ok_FB)
        apply (simp add: type_ok_def)
        apply (frule Type_OK_fb_out_less_step, simp_all)
        apply (drule_tac As = "(fb_out_less_step (out A) As)" in type_ok_parallel_list)
        apply (drule Type_ok_FB)
        apply (simp add: type_ok_def)
        apply (frule FB_Var_fb_out_less_step, simp_all)
        apply (simp add: FB_def Let_def In_Parallel )
        apply (simp add: FB_Var_def)
        apply (simp add: set_diff fb_out_less_step_def fb_less_step_def)
        apply (simp add: mem_get_other_out mem_get_comp_out)
        apply (subst union_set_In_CompA, simp_all)
        apply (simp add: Type_OK_def)
        apply (simp add: set_diff)
        apply (rule BBBB_f, simp_all)
        apply (simp add: set_eq_iff set_diff, auto)
        by (simp add: Type_OK_loop_free_elem)


      lemma diff_cons: "(x \<ominus> (a # y)) = (x \<ominus> [a] \<ominus> y)"
        by (induction x, simp_all)

      lemma [simp]: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow>
          FB_Var (Parallel_list As) = a # L \<Longrightarrow>  
          Out (FB (Parallel_list (fb_out_less_step a As))) = Out (FB (Parallel_list As))"
        apply (frule FB_Var_cons_out, simp_all, safe)
        apply (frule FB_Var_fb_out_less_step, simp_all)
        apply (simp add: FB_def Let_def FB_Var_def)
        apply (simp add: Out_Parallel)
        apply (subst map_Out_fb_out_less_step, simp_all)
        apply (simp add: concat_map_Out_get_other_out)
        by (subst diff_cons, simp)

      lemma TI_Parallel_list: "(\<forall> A \<in> set As . type_ok A) \<Longrightarrow> TI (Trs (Parallel_list As)) = TVs (op_list [] op \<oplus> (map In As))"
        apply (induction As)
        apply simp
        apply (simp add: ParallelId_def)
        apply simp
        apply (simp add: Parallel_def)
        apply (subst TI_comp)
        apply simp_all
        apply (simp_all add: In_Parallel)
        by (simp add: type_ok_def)

      lemma TO_Parallel_list: "(\<forall> A \<in> set As . type_ok A) \<Longrightarrow> TO (Trs (Parallel_list As)) = TVs (concat (map Out As))"
        apply (induction As, simp_all)
        apply (simp add: ParallelId_def)
        apply (simp add: Parallel_def)
        apply (subst TO_comp)
        apply simp_all
        apply (simp_all add: In_Parallel TI_Parallel_list)
        by (simp_all add: type_ok_def)

      lemma fbtype_aux: "(Type_OK As) \<Longrightarrow> loop_free As \<Longrightarrow> FB_Var (Parallel_list As) = a # L \<Longrightarrow>
            fbtype ([L @ (In (Parallel_list (fb_out_less_step a As)) \<ominus> L) \<leadsto> In (Parallel_list (fb_out_less_step a As))] oo Trs (Parallel_list (fb_out_less_step a As)) oo
              [Out (Parallel_list (fb_out_less_step a As)) \<leadsto> L @ (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L)])
              (TVs L) (TO [In (Parallel_list As) \<ominus> a # L \<leadsto> In (Parallel_list (fb_out_less_step a As)) \<ominus> L]) (TVs (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L))"
        apply (frule Type_OK_fb_out_less_step, simp_all)
        apply (simp add: fbtype_def, safe)
        apply (subst TI_comp, simp_all)
        apply (subst TO_comp, simp_all)
        apply (simp add: In_Parallel)
        apply (subst TI_Parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (simp add: Out_Parallel)
        apply (subst TO_Parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (subst TI_comp, simp_all)
        apply (simp add: In_Parallel)
        apply (subst TI_Parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (subst TO_comp, simp_all)
        apply (subst TO_comp, simp_all)
        apply (simp add: In_Parallel)
        apply (subst TI_Parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (simp add: Out_Parallel)
        apply (subst TO_Parallel_list)
        apply (simp add: Type_OK_def)
        by simp
 

      lemma fb_indep_left_a: "fbtype S tsa (TO A) ts \<Longrightarrow> A oo (fb^^(length tsa)) S = (fb^^(length tsa)) ((ID tsa \<parallel> A) oo S)" 
        by (simp add: fb_indep_left)


      lemma parallel_list_cons: "parallel_list (A # As) = A \<parallel> parallel_list As"
        by (simp add: parallel_list_def)
  
      lemma TI_parallel_list: "(\<forall> A \<in> set As . type_ok A) \<Longrightarrow> TI (parallel_list (map Trs As)) = TVs (concat (map In As))"
        apply (induction As)
        by (simp_all add: parallel_list_def type_ok_def)
  
      lemma TO_parallel_list: "(\<forall> A \<in> set As . type_ok A) \<Longrightarrow>TO (parallel_list (map Trs As)) = TVs (concat (map Out As))"
        apply (induction As)
        by (simp_all add: parallel_list_def type_ok_def)


      lemma Trs_Parallel_list_aux_a: "Type_OK As \<Longrightarrow> type_ok a \<Longrightarrow>
            [In a \<oplus> In (Parallel_list As) \<leadsto> In a @ In (Parallel_list As)] oo Trs a \<parallel> ([In (Parallel_list As) \<leadsto> concat (map In As)] oo parallel_list (map Trs As)) =
            [In a \<oplus> In (Parallel_list As) \<leadsto> In a @ In (Parallel_list As)] oo ([In a \<leadsto> In a ] \<parallel> [In (Parallel_list As) \<leadsto> concat (map In As)] oo Trs a \<parallel> parallel_list (map Trs As))"
        apply (subst comp_parallel_distrib)
        apply (simp add:   type_ok_def)
        apply (simp )
        apply (subst TI_parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (subst comp_id_switch) 
        by (simp_all add: type_ok_def)
  
      lemma Trs_Parallel_list_aux_b :"distinct x \<Longrightarrow> distinct y \<Longrightarrow>  set z \<subseteq> set y \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> x] \<parallel> [y \<leadsto> z] = [x \<oplus> y \<leadsto> x @ z]"
        by (subst switch_par_comp_Subst, simp_all add: distinct_addvars set_addvars Subst_eq)
  
  
      lemma Trs_Parallel_list: "Type_OK As \<Longrightarrow> Trs (Parallel_list As) = [In (Parallel_list As) \<leadsto> concat (map In As)] oo parallel_list (map Trs As)"
        apply (induction As)
        apply (simp add: Parallel_list_def ParallelId_def parallel_list_def)
        apply (simp add: distinct_id)
        apply simp
        apply (simp add: Parallel_def Let_def parallel_list_cons)
        apply (simp add: Type_OK_cons)
        apply (simp add: Trs_Parallel_list_aux_a)
        apply (subst comp_assoc[THEN sym])
        apply (simp_all)
        apply (simp add: type_ok_def)
        apply (subst TI_parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (subst Trs_Parallel_list_aux_b)
        apply (simp add: type_ok_def)
        using type_ok_def type_ok_parallel_list apply blast
        apply (subst In_Parallel)
        by auto
  
  
      (*to delete and use perm_set_eq instead*)
      lemma perm_set: "perm x y \<Longrightarrow> set x \<subseteq> set y"
        by simp


      lemma CompA_Id[simp]: "CompA A \<box> = \<box>"
        by (simp add: CompA_def comp_def ParallelId_def)

      lemma type_ok_ParallelId[simp]: "type_ok \<box>"
        by (simp add: type_ok_def ParallelId_def)



      lemma in_equiv_aux_a :"distinct x \<Longrightarrow> distinct y \<Longrightarrow>  set z \<subseteq> set x \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> z] \<parallel> [y \<leadsto> y] = [x \<oplus> y \<leadsto> z @ y]"
        by (subst switch_par_comp_Subst, simp_all add: distinct_addvars set_addvars Subst_eq)


      lemma in_equiv_Parallel_aux_d: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set u \<subseteq> set x \<Longrightarrow> perm y v \<Longrightarrow> [x \<oplus> y \<leadsto> x @ v] oo [x \<leadsto> u] \<parallel> [v \<leadsto> v] = [x \<oplus> y \<leadsto> u @ v]"
        proof -
          assume [simp]: "distinct x"
          assume [simp]: "distinct y"
          assume [simp]: "set u \<subseteq> set x"
          assume [simp]: "perm y v"

          def v' \<equiv> "newvars x (TVs v)"

          have [simp]: "distinct v"
            apply (subgoal_tac "perm y v")
            apply (subgoal_tac "distinct y")
            using dist_perm apply blast
            by simp_all

          have [simp]: "distinct v'"
            by (simp add: v'_def)

          have [simp]: "set x \<inter> set v' = {}"
            by (simp add: v'_def)

          have [simp]: "distinct (x \<oplus> y)"
            by (simp add: distinct_addvars)

          have [simp]: "set v' \<inter> set u = {}"
            apply (subgoal_tac "set v' \<inter> set x = {}")
            apply (subgoal_tac "set u \<subseteq> set x")
            apply blast
            apply simp
            using \<open>set x \<inter> set v' = {}\<close> by blast

          have A: "TVs v' = TVs v"
            by (simp add: v'_def)
            
          have [simp]: "length v' = length v"
            by (metis \<open>TVs v' = TVs v\<close> length_TVs)

          have [simp]: "Subst (x @ v') (x @ v) (u @ v') = u @ v"
            apply (simp add: Subst_append)
            apply (subst Subst_not_in)
            apply (simp_all)
            apply (subst Subst_not_in_a)
            by (simp_all add: Subst_eq)

          have "[x \<oplus> y \<leadsto> x @ v] oo [x \<leadsto> u] \<parallel> [v \<leadsto> v] = [x \<oplus> y \<leadsto> x @ v] oo [x \<leadsto> u] \<parallel> [v' \<leadsto> v']"
            by (simp add: v'_def switch_newvars)
          also have "... = [x \<oplus> y \<leadsto> x @ v] oo [x @ v' \<leadsto> u @ v']"
            apply (subst par_switch)
            by (simp_all)
          also have "... = [x \<oplus> y \<leadsto> u @ v]"
            apply (subst switch_comp_subst)
            apply (simp_all)
            apply (simp add: set_addvars)
            using \<open>perm y v\<close> perm_set_eq apply blast
            apply (simp add: le_supI1)
            by (simp add: v'_def)
          finally show ?thesis
            by simp
        qed

      lemma comp_par_switch_subst: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set u \<subseteq> set x \<Longrightarrow> set v \<subseteq> set y \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> u] \<parallel> [y \<leadsto> v] = [x \<oplus> y \<leadsto> u @ v]"
        proof -
          assume [simp]: "distinct x"
          assume [simp]: "distinct y"
          assume [simp]: "set u \<subseteq> set x"
          assume [simp]: "set v \<subseteq> set y"
        
          def x' \<equiv> "newvars (x@y) (TVs x)"

          have [simp]: "distinct x'"
            by (simp add: x'_def)

          have [simp]: "set x \<inter> set x' = {}"
            by (metis Int_empty_right inf.commute inf.left_commute inf_sup_absorb newvars_old_distinct set_append x'_def)

          have [simp]: "TVs x = TVs x'"
            by (simp add: x'_def)

          have [simp]: "length x = length x'"
            by (metis \<open>TVs x = TVs x'\<close> length_TVs)

          have [simp]: "set x' \<inter> set y = {}"
            by (metis Diff_disjoint diff_distinct diff_inter_left diff_union inf_bot_left newvars_old_distinct_a set_diff set_inter x'_def)            

          have [simp]: "set (Subst x x' u) \<subseteq> set x'"
            by (simp add: Subst_set_incl)

          have [simp]: "distinct (x \<oplus> y)"
            by (simp add: distinct_addvars)

          have [simp]: "set y \<inter> set (Subst x x' u) = {}"
            apply (subgoal_tac "set (Subst x x' u) \<subseteq> set x'")
            apply (subgoal_tac "set y \<inter> set x' = {}")
            apply blast
            by (simp_all add: Int_commute)

          have [simp]: "set x' \<inter> set v = {}"
            apply (subgoal_tac "set v \<subseteq> set y")
            apply (subgoal_tac "set x' \<inter> set y = {}")
            apply blast
            by simp_all

          have [simp]: "Subst (x' @ y) (x @ y) ((Subst x x' u) @ v) = u @ v"
            apply (simp add: Subst_append)
            apply (subst Subst_not_in, simp_all)
            apply (subst Subst_not_in_a, simp_all)
            by (simp add: Subst_eq)
         

          have "[x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> u] \<parallel> [y \<leadsto> v] = [x \<oplus> y \<leadsto> x @ y] oo [Subst x x' x \<leadsto> Subst x x' u] \<parallel> [y \<leadsto> v]"
            apply (cut_tac u=x and v=x' and x=x and y=u in Subst_switch_more_general)
            apply simp_all
            by (simp add: Int_commute)
          also have "... = [x \<oplus> y \<leadsto> x @ y] oo [x' \<leadsto> Subst x x' u] \<parallel> [y \<leadsto> v]"
            by simp
          also have "... = [x \<oplus> y \<leadsto> x @ y] oo [x' @ y \<leadsto> (Subst x x' u) @ v]"
            by (simp add: par_switch)
          also have "... = [x \<oplus> y \<leadsto> Subst (x' @ y) (x @ y) ((Subst x x' u) @ v)]"
            apply (subst switch_comp_subst, simp_all add: set_addvars)
            apply safe
            using \<open>set (Subst x x' u) \<subseteq> set x'\<close> apply blast
            using \<open>set v \<subseteq> set y\<close> by blast
          also have "... = [x \<oplus> y \<leadsto> u @ v]"
            by simp_all

          finally show ?thesis
            by simp
        qed

      lemma in_equiv_Parallel_aux_b :"distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm u x \<Longrightarrow> perm y v \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> u] \<parallel> [y \<leadsto> v] = [x \<oplus> y \<leadsto> u @ v]"
        by (subst comp_par_switch_subst, simp_all )

      lemma [simp]: "set x \<subseteq> set (x \<oplus> y)"
        by (simp add: set_addvars)
      lemma [simp]: "set y \<subseteq> set (x \<oplus> y)"
        by (simp add: set_addvars)

      declare distinct_addvars [simp]

      lemma in_equiv_Parallel: "type_ok B \<Longrightarrow> type_ok B' \<Longrightarrow> in_equiv A B \<Longrightarrow> in_equiv A' B' \<Longrightarrow> in_equiv (A ||| A') (B ||| B')"
        apply (frule in_equiv_type_ok, simp_all)
        apply (frule_tac A = A' in in_equiv_type_ok, simp)
        apply (frule_tac A = A in in_equiv_type_ok, simp)
        apply (simp add: in_equiv_def type_ok_def, safe)
        apply (simp add: Parallel_def)
        apply (subst comp_parallel_distrib[THEN sym], simp_all)
        apply (subst comp_assoc[THEN sym], simp_all)
        apply (subst comp_par_switch_subst, simp_all)
        apply (subst comp_assoc[THEN sym], simp_all)
        by (simp add: switch_comp)


      (*todo: change name to Out_CompA*)
      thm local.BBB_a

      lemma map_Out_CompA: "length (Out A) = 1 \<Longrightarrow> map (out \<circ> CompA A) As = map out As"
        by (induction As, simp_all add: BBB_a out_def)

      lemma CompA_in[simp]: "length (Out A) = 1 \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> CompA A B = A ;; B"
        by (simp add: CompA_def)

      lemma CompA_not_in[simp]: "length (Out A) = 1 \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> CompA A B = B"
        by (simp add: CompA_def)


      lemma [simp]: "x \<oplus> y \<oplus> x = x \<oplus> y"
        apply (simp add: addvars_def)
        by (simp add: diff_eq diff_union)


      thm subst.simps

      lemma  AA: "\<And> y . distinct y \<Longrightarrow> length x = length y \<Longrightarrow> a \<in> set x \<Longrightarrow> subst y x (subst x y a) = a"
        by (induction x, auto)
              

      lemma AAa: "distinct y \<Longrightarrow> length x = length y \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> Subst y x (Subst x y z) = z"
        apply (induction z)
        by (simp_all add: AA)
        

      lemma comp_par: "distinct x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> [x \<leadsto> x @ x] oo [x \<leadsto> y] \<parallel> [x \<leadsto> y] = [x \<leadsto> y @ y]"
        by (subst switch_par_comp_Subst, simp_all add: set_addvars Subst_eq)

      (*
      definition "deterministic A = (let x = newvars [] (TI A) in let y = newvars [] (TO A) in [x \<leadsto> x @ x] oo (A \<parallel> A) = A oo [y \<leadsto> y @ y])"
      *)

      thm Subst_switch_more_general
      thm switch_comp_subst

      lemma Subst_switch_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> TVs x = TVs y \<Longrightarrow> [x \<leadsto> z] = [y \<leadsto> Subst x y z]"
        by (metis distinct_id order_refl switch_comp_a switch_comp_subst)

       lemma change_var_names: "distinct a \<Longrightarrow> distinct b \<Longrightarrow> TVs a = TVs b \<Longrightarrow> [a \<leadsto> a @ a] = [b \<leadsto> b @ b]"
        by (simp add: Switch_Split)


      lemma deterministicE: "deterministic A \<Longrightarrow> distinct x \<Longrightarrow> distinct y \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs y 
        \<Longrightarrow> [x \<leadsto> x @ x] oo (A \<parallel> A) = A oo [y \<leadsto> y @ y]"
        by (simp add: deterministic_def Switch_Split)

      lemma deterministicI: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> TI A = TVs x \<Longrightarrow> TO A = TVs y \<Longrightarrow> 
        [x \<leadsto> x @ x] oo A \<parallel> A = A oo [y \<leadsto> y @ y] \<Longrightarrow> deterministic A"
        by (simp add: deterministic_def Switch_Split)

      lemma in_equiv_CompA_Parallel_a: " deterministic (Trs A) \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> out A \<in> set (In C) \<Longrightarrow> 
              in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        apply (simp add: in_equiv_def, safe)
        apply (simp add: In_CompA set_addvars)
        apply (simp_all add: Comp_def CompA_def Parallel_def Let_def Var_def set_addvars diff_inter_right diff_inter_left)
        apply (simp_all add: Out_out par_empty_left)
        apply (simp add: addvars_assoc [THEN sym])
        apply (metis addvars_assoc addvars_minus perm_def)
        apply (simp_all add: set_addvars)
        proof -
          assume [simp]: "deterministic (Trs A)"
          assume [simp]: "length (Out A) = Suc 0"
          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"
          assume [simp]: "type_ok C"
          assume [simp]: "out A \<in> set (In B)"
          assume [simp]: "out A \<in> set (In C)"

          def IA \<equiv> "In A"
          def IB \<equiv> "In B"
          def IC \<equiv> "In C"
          def OA \<equiv> "Out A"
          def IBA \<equiv> "IB \<ominus> OA"
          def ICA \<equiv> "IC \<ominus> OA"

          def IBA' \<equiv> "newvars (IA @ OA @ ICA @ IBA) (TVs IBA)"
          def IA' \<equiv> "newvars (IBA' @ IA @ ICA) (TVs IA)"
          def ICA' \<equiv> "newvars (IA' @ IBA' @ IA @ OA) (TVs ICA)"
          def OA' \<equiv> "newvars (OA @ IBA' @ ICA' @ IBA @ ICA @ IA) (TVs OA)"

          have [simp]: "TVs IA = TI (Trs A)"
            using \<open>type_ok A\<close> type_ok_def IA_def by fastforce

          have [simp]: "distinct IA"
            using \<open>type_ok A\<close> type_ok_def IA_def by fastforce

          have [simp]: "TVs OA = TO (Trs A)"
            using \<open>type_ok A\<close> type_ok_def OA_def by fastforce

          have [simp]: "distinct OA "
            using \<open>type_ok A\<close> type_ok_def OA_def by fastforce
            
          have [simp]: "TVs IB = TI (Trs B)"
            using \<open>type_ok B\<close> type_ok_def IB_def by fastforce

          have [simp]: "distinct IB"
            using \<open>type_ok B\<close> type_ok_def IB_def by fastforce

          have [simp]: "TVs IC = TI (Trs C)"
            using \<open>type_ok C\<close> type_ok_def IC_def by fastforce

          have [simp]: "distinct IC"
            using \<open>type_ok C\<close> type_ok_def IC_def by fastforce

          have [simp]: "distinct IBA"
            by (simp add: IBA_def)

          have [simp]: "distinct ICA"
            by (simp add: ICA_def)

          have [simp]: "distinct (IA \<oplus> IBA)"
            by (simp)

          have [simp]: "distinct (IA \<oplus> ICA)"
            by (simp)

          have [simp]: "distinct IBA'"
            by (simp add: IBA'_def)

          have [simp]: "set IBA' \<inter> set IA = {}"
            by (metis IBA'_def Int_commute bot_eq_sup_iff inf_sup_distrib2 newvars_old_distinct_a set_append)

          have a[simp]: "set OA \<inter> set IBA' = {}"
            by (metis IBA'_def bot_eq_sup_iff inf_sup_distrib2 newvars_old_distinct_a set_append)

          have [simp]: "set IBA' \<inter> set ICA = {}"
            by (metis IBA'_def Int_commute bot_eq_sup_iff inf_sup_distrib2 newvars_old_distinct_a set_append)

          have [simp]: "TVs IBA' = TVs IBA"
            by (simp add: IBA'_def)

          have [simp]: "distinct IA'"
            by (simp add: IA'_def)

          have [simp]: "set IA' \<inter> set IBA' = {}"
            by (metis IA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set IA' \<inter> set IA = {}"
            by (metis IA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]:"distinct ICA'"
            by (simp add: ICA'_def)

          have [simp]: "set IA \<inter> set ICA' = {}"
            by (metis ICA'_def Int_empty_right inf_commute inf_left_commute inf_sup_absorb inf_sup_aci(5) newvars_old_distinct set_append)

          have [simp]: "set IBA' \<inter> set ICA' = {}"
            by (metis ICA'_def Int_empty_right inf_commute inf_left_commute inf_sup_absorb inf_sup_aci(5) newvars_old_distinct set_append)

          have [simp]: "set IA' \<inter> set ICA' = {}"
            by (metis ICA'_def Int_empty_right inf_commute inf_left_commute inf_sup_absorb newvars_old_distinct set_append)

          have [simp]: "TVs (IA') = TI (Trs A) "
            by (simp add: IA'_def)

          have [simp]: "TVs ICA = TVs ICA'"
            by (simp add: ICA'_def)

          have [simp]: "length IA' = length IA"
            by (simp add: TVs_length_eq)

          have [simp]: "length IBA' = length IBA"
            by (metis \<open>TVs IBA' = TVs IBA\<close> length_TVs)

          have [simp]: "length ICA' = length ICA"
            by (metis \<open>TVs ICA = TVs ICA'\<close> length_TVs)

          have [simp]: "Subst (IA' @ IBA' @ IA @ ICA') (IA @ IBA @ IA @ ICA) IA' = IA"
            apply (subst Subst_not_in, simp_all)
            by (simp add: Int_commute)

          have [simp]: "Subst (IA' @ IBA' @ IA @ ICA') (IA @ IBA @ IA @ ICA) IA = IA"
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in_a, simp_all)
            by (subst Subst_not_in, simp_all add: Int_commute)

          have [simp]: "Subst (IA' @ IBA' @ IA @ ICA') (IA @ IBA @ IA @ ICA) IBA' = IBA"
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in, simp_all add: Int_commute)
            using \<open>set IBA' \<inter> set IA = {}\<close> by blast

          have [simp]: "Subst (IA' @ IBA' @ IA @ ICA') (IA @ IBA @ IA @ ICA) ICA' = ICA"
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in_a, simp_all)
            by (subst Subst_not_in_a, simp_all)

          have [simp]: "Subst (IA' @ IBA' @ IA @ ICA') (IA @ IBA @ IA @ ICA) (IA' @ IA @ IBA' @ ICA') = IA @ IA @ IBA @ ICA"
            by (simp add: Subst_append)

          have [simp]: "distinct OA'"
            by (simp add: OA'_def)

          have [simp]: "TVs OA' = TO (Trs A)"
            by (simp add: OA'_def)

          have [simp]: "set OA' \<inter> set OA = {}"
            by (metis OA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA' \<inter> set IBA' = {}"
            by (metis OA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA' \<inter> set ICA' = {}"
            by (metis OA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA' \<inter> set IBA = {}"
            by (metis OA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA' \<inter> set ICA = {}"
            by (metis OA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA \<inter> set ICA' = {}"
            by (metis ICA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set IBA' \<inter> set IBA = {}"
            by (metis IBA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set IBA \<inter> set OA = {}"
            apply (simp add: IBA_def set_diff)
            by blast

          have [simp]: "length OA = length OA'"
            by (simp add: TVs_length_eq)

          have [simp]: "[IA \<leadsto> IA @ IA] oo Trs A \<parallel> Trs A = Trs A oo [OA \<leadsto> OA @ OA]"
            apply (subgoal_tac "deterministic (Trs A)")
            apply (simp add: deterministicE)
            by simp

          have [simp]: "Subst (OA' @ OA @ IBA' @ ICA') (OA @ OA @ IBA' @ ICA) OA' = OA"
            apply (subst Subst_not_in, simp_all)
            using \<open>set OA' \<inter> set IBA' = {}\<close> \<open>set OA' \<inter> set ICA' = {}\<close> \<open>set OA' \<inter> set OA = {}\<close> by blast

          have [simp]: "Subst (OA' @ OA @ IBA' @ ICA') (OA @ OA @ IBA' @ ICA) IBA' = IBA'"
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in, simp_all)
            by (simp add: Int_commute)

          have [simp]: "Subst (OA' @ OA @ IBA' @ ICA') (OA @ OA @ IBA' @ ICA) OA = OA "
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in, simp_all)
            by (metis Int_commute Un_absorb \<open>set OA \<inter> set ICA' = {}\<close> a inf_sup_distrib2)
            
          have [simp]: "Subst (OA' @ OA @ IBA' @ ICA') (OA @ OA @ IBA' @ ICA) ICA' = ICA"
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in_a, simp_all)
            by (subst Subst_not_in_a, simp_all)

          have [simp]: "Subst (OA' @ OA @ IBA' @ ICA') (OA @ OA @ IBA' @ ICA) (OA' @ IBA' @ OA @ ICA') = OA @ IBA' @ OA @ ICA"
            by (simp add: Subst_append)

          have [simp]: "distinct (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA))"
            by (simp)

          have [simp]: "perm (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) (IA \<oplus> (IB \<oplus> IC \<ominus> OA))"
            apply (simp add: IBA_def ICA_def)
            by (metis diff_eq addvars_assoc addvars_def addvars_empty addvars_minus perm_tp perm_trans)

          have [simp]: "distinct (IB \<oplus> IC \<ominus> OA)"
            by (simp )

          have [simp]: "set OA \<inter> set (IB \<oplus> IC \<ominus> OA) = {}"
            by (simp add: set_diff)

          have [simp]: "OA \<otimes> IB = OA"
            by (simp add: OA_def IB_def Out_out)

          have [simp]: "OA \<otimes> IC = OA"
            by (simp add: OA_def IC_def Out_out)

          have [simp]: "OA \<otimes> (IB \<oplus> IC) = OA"
            apply (simp add: addvars_def)
            by (metis (mono_tags, lifting) diff_eq Diff_Int_distrib \<open>OA \<otimes> IB = OA\<close> \<open>OA \<otimes> IC = OA\<close> empty_set inter_addvars_empty set_diff set_inter)
            
          have [simp]: "perm (OA @ (IB \<oplus> IC \<ominus> OA)) (IB \<oplus> IC)"
            by (subst perm_aux_a, simp_all)

          have [simp]: "set OA' \<inter> set IA = {}"
            by (metis OA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA' \<inter> set (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) = {}"
            by (simp add: set_addvars)

          have [simp]: "Subst (OA @ IBA' @ ICA) (OA' @ IBA @ ICA) OA = OA'"
            apply (subst Subst_not_in, simp_all)
            by (metis Diff_disjoint ICA_def Int_Un_distrib2 Un_empty_left a inf_commute set_diff)

          have [simp]: "Subst (OA @ IBA' @ ICA) (OA' @ IBA @ ICA) IBA' = IBA"
            apply (subst Subst_not_in_a, simp_all)
            apply (subst Subst_not_in, simp_all)
            by (simp add: Int_commute)

          have [simp]: "Subst (OA @ IBA' @ ICA) (OA' @ IBA @ ICA) ICA = ICA"
            apply (subst Subst_not_in_a, simp_all)
            apply (simp add: ICA_def set_diff)
            by (subst Subst_not_in_a, simp_all)

          have [simp]: "Subst (OA @ IBA' @ ICA) (OA' @ IBA @ ICA) (OA @ IBA' @ OA @ ICA) = OA' @ IBA @ OA' @ ICA"
            by (simp add: Subst_append)

          have [simp]: "Subst (OA @ (IBA \<oplus> ICA)) (OA' @ (IBA \<oplus> ICA)) IB = Subst (OA @ IBA) (OA' @ IBA) IB"
            apply (subst Subst_cancel_left, simp_all)
            apply (simp add: IBA_def ICA_def set_addvars set_diff)
            apply (subst Subst_cancel_left, simp_all)
            by (simp add: IBA_def set_addvars set_diff)

          have [simp]: "Subst (OA @ (IBA \<oplus> ICA)) (OA' @ (IBA \<oplus> ICA)) IC = Subst (OA @ ICA) (OA' @ ICA) IC"
            apply (subst Subst_cancel_left, simp_all)
            apply (simp add: IBA_def ICA_def set_addvars set_diff)
            apply (subst Subst_cancel_left, simp_all)
            by (simp add: ICA_def set_addvars set_diff)
            
          have [simp]: "Subst (OA @ (IBA \<oplus> ICA)) (OA' @ (IBA \<oplus> ICA)) (IB @ IC) = (Subst (OA @ IBA) (OA' @ IBA ) IB) @ (Subst (OA @ ICA) (OA' @ ICA) IC)"
            by (simp add: Subst_append)

            
          have A: "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In A \<oplus> (In C \<ominus> [out A])) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ (In A \<oplus> (In C \<ominus> [out A]))] oo
                ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
                ([In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo [out A # (In C \<ominus> [out A]) \<leadsto> In C] oo Trs C) =
                [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo 
                ([OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
            proof -
              have "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In A \<oplus> (In C \<ominus> [out A])) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ (In A \<oplus> (In C \<ominus> [out A]))] oo
                  ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
                  ([In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo [out A # (In C \<ominus> [out A]) \<leadsto> In C] oo Trs C) =
                  [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA \<oplus> IBA) @ (IA \<oplus> ICA)] oo
                  ([IA \<oplus> IBA \<leadsto> IA @ IBA] oo Trs A \<parallel> [IBA \<leadsto> IBA] oo [OA @ IBA \<leadsto> IB] oo Trs B) \<parallel>
                  ([IA \<oplus> ICA \<leadsto> IA @ ICA] oo Trs A \<parallel> [ICA \<leadsto> ICA] oo [OA @ ICA \<leadsto> IC] oo Trs C)"
                by (simp add: IA_def IB_def IC_def IBA_def ICA_def OA_def Out_out)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA \<oplus> IBA) @ (IA \<oplus> ICA)] oo
                  ([IA \<oplus> IBA \<leadsto> IA @ IBA] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo
                   (Trs A \<parallel> [IBA \<leadsto> IBA]) \<parallel> (Trs A \<parallel> [ICA \<leadsto> ICA]) oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C)"
                by (simp add: comp_parallel_distrib )
              also have "... = ([(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA \<oplus> IBA) @ (IA \<oplus> ICA)] oo [IA \<oplus> IBA \<leadsto> IA @ IBA] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA]) oo
                   (Trs A \<parallel> [IBA \<leadsto> IBA]) \<parallel> (Trs A \<parallel> [ICA \<leadsto> ICA]) oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_assoc )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   (Trs A \<parallel> [IBA \<leadsto> IBA]) \<parallel> (Trs A \<parallel> [ICA \<leadsto> ICA]) oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (subst comp_par_switch_subst)
                by (simp_all add: set_addvars)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   Trs A \<parallel> ([IBA \<leadsto> IBA] \<parallel> Trs A) \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: par_assoc)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   Trs A \<parallel> ([IBA' \<leadsto> IBA'] \<parallel> Trs A) \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: IBA'_def switch_newvars)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   Trs A \<parallel> ([IBA' @ IA \<leadsto> IA @ IBA'] oo Trs A \<parallel> [IBA' \<leadsto> IBA'] oo [OA @ IBA' \<leadsto> IBA' @ OA]) \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (cut_tac y=IA and x="IBA'" and T="Trs A" and S="[IBA' \<leadsto> IBA']" and u=OA and v="IBA'" in switch_par)
                by simp_all
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   ([IA \<leadsto> IA] \<parallel> [IBA' @ IA \<leadsto> IA @ IBA'] \<parallel> [ICA \<leadsto> ICA] oo Trs A \<parallel> (Trs A \<parallel> [IBA' \<leadsto> IBA']) \<parallel> [ICA \<leadsto> ICA] oo [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA]) oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_parallel_distrib )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   [IA \<leadsto> IA] \<parallel> [IBA' @ IA \<leadsto> IA @ IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   Trs A \<parallel> (Trs A \<parallel> [IBA' \<leadsto> IBA']) \<parallel> [ICA \<leadsto> ICA] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_assoc  )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   [IA \<leadsto> IA] \<parallel> [IBA' @ IA \<leadsto> IA @ IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' \<leadsto> IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: par_assoc)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   [IA' \<leadsto> IA'] \<parallel> [IBA' @ IA \<leadsto> IA @ IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' \<leadsto> IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: IA'_def distinct_id)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   [IA' \<leadsto> IA'] \<parallel> [IBA' @ IA \<leadsto> IA @ IBA'] \<parallel> [ICA' \<leadsto> ICA'] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' \<leadsto> IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (metis (full_types) switch_newvars ICA'_def \<open>distinct ICA\<close>)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> (IA @ IBA) @ (IA @ ICA)] oo
                   [IA' @ IBA' @ IA @ ICA' \<leadsto> IA' @ IA @ IBA' @ ICA'] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' \<leadsto> IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (subst par_switch, simp_all)
                apply (subst par_switch, simp_all)
                by auto
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IA @ IBA @ ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' \<leadsto> IBA'] \<parallel> [ICA \<leadsto> ICA] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (subst switch_comp_subst, simp_all )
                by (auto simp add: IA_def IBA_def IB_def OA_def ICA_def IC_def set_diff set_inter set_addvars)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IA @ IBA @ ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' @ ICA  \<leadsto> IBA' @ ICA ] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA \<leadsto> ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (simp add: par_assoc)
                by (subst par_switch, simp_all)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IA @ IBA @ ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' @ ICA  \<leadsto> IBA' @ ICA ] oo 
                   [OA \<leadsto> OA] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA' \<leadsto> ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (metis (full_types) switch_newvars ICA'_def \<open>distinct ICA\<close>)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IA @ IBA @ ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' @ ICA  \<leadsto> IBA' @ ICA ] oo 
                   [OA' \<leadsto> OA'] \<parallel> [OA @ IBA' \<leadsto> IBA' @ OA] \<parallel> [ICA' \<leadsto> ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (metis switch_newvars  OA'_def \<open>distinct OA\<close>)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IA @ IBA @ ICA] oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' @ ICA  \<leadsto> IBA' @ ICA ] oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (subst par_switch, simp_all)
                apply (subst par_switch, simp_all)
                by blast
              also have "... = ([(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo [IA \<leadsto> IA @ IA] \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA]) oo 
                   (Trs A \<parallel> Trs A) \<parallel> [IBA' @ ICA  \<leadsto> IBA' @ ICA ] oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (subst switch_par_comp_Subst, simp_all add: set_addvars Subst_eq )
                apply blast
                by blast
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   ([IA \<leadsto> IA @ IA] \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo (Trs A \<parallel> Trs A) \<parallel> [IBA' @ ICA  \<leadsto> IBA' @ ICA ]) oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_assoc  )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   (([IA \<leadsto> IA @ IA] oo (Trs A \<parallel> Trs A)) \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA]) oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_parallel_distrib)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   ((Trs A oo [OA \<leadsto> OA @ OA]) \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA]) oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                 by simp
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   (Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo [OA \<leadsto> OA @ OA] \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA]) oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_parallel_distrib)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   (Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo [OA @ IBA' @ ICA \<leadsto> OA @ OA @ IBA' @ ICA]) oo 
                   [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA'] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                apply (subst par_switch, simp_all)
                by (simp add: ICA_def set_diff)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo 
                   ([OA @ IBA' @ ICA \<leadsto> OA @ OA @ IBA' @ ICA] oo [OA' @ OA @ IBA' @ ICA' \<leadsto> OA' @ IBA' @ OA @ ICA']) oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by (simp add: comp_assoc  )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo 
                   [OA @ IBA' @ ICA \<leadsto> Subst (OA' @ OA @ IBA' @ ICA') (OA @ OA @ IBA' @ ICA) (OA' @ IBA' @ OA @ ICA')] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                 apply (subst switch_comp_subst, simp_all)
                 apply (simp_all add: ICA_def set_diff)
                 by auto
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo 
                   [OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo
                   [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo
                   Trs B \<parallel> Trs C"
                by simp
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IBA @ ICA] oo 
                   Trs A  \<parallel> [IBA' @ ICA \<leadsto> IBA' @ ICA] oo 
                   ([OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"              
                by (simp add: comp_assoc  )
              finally show ?thesis
                by simp
            qed

          have B: "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In A \<oplus> (In C \<ominus> [out A])) \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> [out A])] oo
              ([In A \<oplus> (In B \<oplus> In C \<ominus> [out A]) \<leadsto> In A @ (In B \<oplus> In C \<ominus> [out A])] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> [out A] \<leadsto> In B \<oplus> In C \<ominus> [out A] ] oo [out A # (In B \<oplus> In C \<ominus> [out A]) \<leadsto> In B \<oplus> In C] oo
              ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C)) =
               [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> IC \<ominus> OA)] oo 
              Trs A \<parallel> [IB \<oplus> IC \<ominus> OA \<leadsto> IB \<oplus> IC \<ominus> OA] oo 
              ([OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C)"
            proof - 
              have "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In A \<oplus> (In C \<ominus> [out A])) \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> [out A])] oo
                  ([In A \<oplus> (In B \<oplus> In C \<ominus> [out A]) \<leadsto> In A @ (In B \<oplus> In C \<ominus> [out A])] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> [out A] \<leadsto> In B \<oplus> In C \<ominus> [out A] ] oo [out A # (In B \<oplus> In C \<ominus> [out A]) \<leadsto> In B \<oplus> In C] oo
                  ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C)) =
                  [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA \<oplus> (IB \<oplus> IC \<ominus> OA)] oo
                  ([IA \<oplus> (IB \<oplus> IC \<ominus> OA) \<leadsto> IA @ (IB \<oplus> IC \<ominus> OA)] oo Trs A \<parallel> [IB \<oplus> IC \<ominus> OA \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB \<oplus> IC] oo
                  ([IB \<oplus> IC \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C))"
                by (simp add: IA_def IB_def IC_def OA_def IBA_def ICA_def Out_out)
              also have "... = ([(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA \<oplus> (IB \<oplus> IC \<ominus> OA)] oo [IA \<oplus> (IB \<oplus> IC \<ominus> OA) \<leadsto> IA @ (IB \<oplus> IC \<ominus> OA)]) oo 
                  Trs A \<parallel> [IB \<oplus> IC \<ominus> OA \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB \<oplus> IC] oo
                  ([IB \<oplus> IC \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C)"
                by (simp add: comp_assoc  )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> IC \<ominus> OA)] oo 
                  Trs A \<parallel> [IB \<oplus> IC \<ominus> OA \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB \<oplus> IC] oo
                  ([IB \<oplus> IC \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C)"
                by (subst switch_comp, simp_all)
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> IC \<ominus> OA)] oo 
                  Trs A \<parallel> [IB \<oplus> IC \<ominus> OA \<leadsto> IB \<oplus> IC \<ominus> OA] oo 
                  (([OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB \<oplus> IC] oo [IB \<oplus> IC \<leadsto> IB @ IC]) oo Trs B \<parallel> Trs C)"
                by (simp add: comp_assoc  )
              also have "... = [(IA \<oplus> IBA) \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> IC \<ominus> OA)] oo 
                  Trs A \<parallel> [IB \<oplus> IC \<ominus> OA \<leadsto> IB \<oplus> IC \<ominus> OA] oo 
                  ([OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C)"
                by (subst switch_comp, simp_all)
              finally show ?thesis
                by simp
            qed

          have C: "[OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IBA @ ICA] oo [OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] =
                   [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> (Subst (OA @ IBA) (OA' @ IBA ) IB) @ (Subst (OA @ ICA) (OA' @ ICA) IC)]"
            proof -
              have "[OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IBA @ ICA] oo [OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] =
                    [OA' \<leadsto> OA'] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IBA @ ICA] oo [OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC]"
                by (metis \<open>distinct OA\<close> OA'_def switch_newvars)
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> OA' @ IBA @ ICA ] oo [OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC]"
                apply (subst par_switch, simp_all add: set_addvars)
                by blast
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> OA' @ IBA @ OA' @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC]"
                apply (subst switch_comp_subst, simp_all)
                apply (simp_all add: ICA_def set_diff)
                by (auto simp add: set_addvars set_diff)
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> (OA' @ IBA) @ (OA' @ ICA)] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC]"
                by simp
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> (Subst (OA @ IBA) (OA' @ IBA ) IB) @ (Subst (OA @ ICA) (OA' @ ICA) IC)]"
                apply (subst switch_par_comp_Subst, simp_all)
                apply (simp add: IBA_def set_diff)
                apply (simp add: ICA_def set_diff)
                apply (simp_all add: set_addvars)
                apply blast
                apply blast
                by (simp_all add: IBA_def ICA_def set_diff)
              finally show ?thesis
                by simp
            qed
         
          have D: "[OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC] = 
                   [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> (Subst (OA @ IBA) (OA' @ IBA ) IB) @ (Subst (OA @ ICA) (OA' @ ICA) IC)]"
            proof -
              have "[OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC] = 
                    [OA' \<leadsto> OA'] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC]"
                by (metis \<open>distinct OA\<close> OA'_def switch_newvars)
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> OA' @ (IB \<oplus> IC \<ominus> OA)] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC]"
                apply (subst par_switch, simp_all)
                apply (simp add: IBA_def ICA_def set_diff set_addvars)
                by blast
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA))  \<leadsto> Subst (OA @ (IB \<oplus> IC \<ominus> OA)) (OA' @ (IB \<oplus> IC \<ominus> OA)) (IB @ IC)]"
                apply (subst switch_comp_subst, simp_all)
                by (auto simp add: set_addvars set_diff OA_def IBA_def IC_def ICA_def)
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> Subst (OA @ (IBA \<oplus> ICA)) (OA' @ (IBA \<oplus> ICA)) (IB @ IC)]"
                by (simp add: addvars_minus IBA_def[THEN symmetric] ICA_def [THEN symmetric])
              also have "... = [OA' @ (IA \<oplus> IBA \<oplus> (IA \<oplus> ICA)) \<leadsto> (Subst (OA @ IBA) (OA' @ IBA ) IB) @ (Subst (OA @ ICA) (OA' @ ICA) IC)]"
                by simp
              finally show ?thesis
                by simp
            qed

          have E: "[OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IBA @ ICA] oo ([OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C) =
                   [OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IB \<oplus> IC \<ominus> OA] oo ([OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C)"
            apply (subgoal_tac "[OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IBA @ ICA] oo [OA @ IBA' @ ICA \<leadsto> OA @ IBA' @ OA @ ICA] oo [OA @ IBA \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] = [OA \<leadsto> OA] \<parallel> [IA \<oplus> IBA \<oplus> (IA \<oplus> ICA) \<leadsto> IB \<oplus> IC \<ominus> OA] oo [OA @ (IB \<oplus> IC \<ominus> OA) \<leadsto> IB @ IC]")
            apply (simp add: comp_assoc [THEN sym]  )
            by (simp add: C D)

          show "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In A \<oplus> (In C \<ominus> [out A])) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ (In A \<oplus> (In C \<ominus> [out A]))] oo
              ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
              ([In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo [out A # (In C \<ominus> [out A]) \<leadsto> In C] oo Trs C) =
              [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In A \<oplus> (In C \<ominus> [out A])) \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> [out A])] oo
              ([In A \<oplus> (In B \<oplus> In C \<ominus> [out A]) \<leadsto> In A @ (In B \<oplus> In C \<ominus> [out A])] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> [out A] \<leadsto> In B \<oplus> In C \<ominus> [out A] ] oo [out A # (In B \<oplus> In C \<ominus> [out A]) \<leadsto> In B \<oplus> In C] oo
              ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C))"
            apply (simp add: A B)
            apply (rule_tac v="OA" in par_switch_eq, simp_all add:   set_addvars set_diff)
            apply blast
            apply blast
            apply (simp add: IBA_def ICA_def set_diff)
            apply blast
            by (simp add: E)
        qed


      thm switch_par_comp_Subst


      lemma in_equiv_CompA_Parallel_c: "length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> out A \<in> set (In C) \<Longrightarrow> 
              in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        apply (simp add: in_equiv_def, safe)
        apply (simp add: Comp_def Let_def In_CompA set_addvars Var_def diff_inter_left diff_inter_right)
        apply (simp add: addvars_minus diff_disjoint Out_out)
        apply (subst set_perm)
        apply (simp add:  type_ok_def )
        apply (simp add:  type_ok_def )
        apply (simp add: set_addvars set_diff)
        apply blast
        apply simp
        apply (simp_all add: Comp_def Let_def BBB_a Var_def)
        apply (simp_all add: Out_out)
        apply (simp add: Let_def Parallel_def In_CompA Var_def Comp_def par_empty_left set_addvars diff_inter_left diff_inter_right Out_out[THEN sym] diff_union)
        apply (simp add: Out_out set_addvars par_empty_left)
        apply (simp add: Out_out[THEN sym])
        proof -
          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"
          assume [simp]: "type_ok C"
          assume [simp]: "length (Out A) = Suc 0"
          assume [simp]: "out A \<notin> set (In B)"
          assume [simp]: "out A \<in> set (In C)"

          def IA \<equiv> "In A"
          def IB \<equiv> "In B"
          def IC \<equiv> "In C"
          def OA \<equiv> "Out A"

          def ICA \<equiv> "IC \<ominus> OA"

          def IB' \<equiv> "newvars (IA @ OA @ ICA) (TVs IB)"

          def ICA' \<equiv> "newvars (IA @ IB' @ OA @ ICA) (TVs ICA)"

          have [simp]: "TVs IB = TI (Trs B)"
            using IB_def \<open>type_ok B\<close> type_ok_def by blast

          have [simp]: "TVs IA = TI (Trs A)"
            using IA_def \<open>type_ok A\<close> type_ok_def by blast

          have [simp]: "TVs OA = TO (Trs A)"
            using OA_def \<open>type_ok A\<close> type_ok_def by blast

          have [simp]: "TVs IC = TI (Trs C)"
            using IC_def \<open>type_ok C\<close> type_ok_def by blast

          have [simp]: "distinct IB"
            using IB_def \<open>type_ok B\<close> type_ok_def by blast

          have [simp]: "distinct IB'"
            by (simp add: IB'_def)

          have [simp]: "distinct IA"
            using IA_def \<open>type_ok A\<close> type_ok_def by blast

          have [simp]: "distinct IC"
            using IC_def \<open>type_ok C\<close> type_ok_def by blast

          have [simp]: "set IB' \<inter> set IA = {}"
            by (metis IB'_def UnCI disjoint_iff_not_equal newvars_old_distinct set_append)

          have [simp]: "distinct OA"
            using OA_def \<open>type_ok A\<close> type_ok_def by blast

          have [simp]: "set OA \<inter> set IB' = {}"
            by (metis IB'_def UnCI disjoint_iff_not_equal newvars_old_distinct set_append)

          have [simp]: "distinct ICA"
            by (simp add: ICA_def )

          have [simp]: "TVs IB' = TI (Trs B)"
            by (simp add: IB'_def)

          have [simp]: "distinct (IA \<oplus> ICA)"
            by (simp )

          have [simp]:"set IB' \<inter> set (ICA) = {}"
            by (metis Diff_disjoint IB'_def diff_disjoint diff_union newvars_old_distinct_a set_diff)

          have [simp]: "set (IA \<oplus> ICA) \<inter> set IB' = {}"
            by (metis Int_commute \<open>set IB' \<inter> set ICA = {}\<close> \<open>set IB' \<inter> set IA = {}\<close> addvars_def empty_inter_diff inter_addvars_empty set_empty set_inter)

          have [simp]: "length IB' = length IB"
            by (simp add: TVs_length_eq)

          have [simp]: "length (IB' @ (IA \<oplus> ICA)) = length (IB @ (IA \<oplus> ICA))"
            by simp          

          have [simp]: "Subst (IB' @ (IA \<oplus> ICA)) (IB @ (IA \<oplus> ICA)) (IB' @ IA @ ICA) = IB @ IA @ ICA"
            by (simp add: Subst_append Subst_not_in Subst_not_in_a Subst_eq)

          have [simp]: "distinct (IB \<oplus> (IA \<oplus> (ICA)))"
            by (simp )

          have [simp]: "distinct (IB' @ (IA \<oplus> ICA))"
            using \<open>distinct (IA \<oplus> ICA)\<close> \<open>distinct IB'\<close> \<open>set (IA \<oplus> ICA) \<inter> set IB' = {}\<close> distinct_append by blast

          have [simp]: "distinct ICA'"
            by (simp add: ICA'_def)

          have [simp]: "set IA \<inter> set ICA' = {}"
            by (metis ICA'_def append_is_Nil_conv empty_inter filter_append inter_filter newvars_old_distinct_a set_inter)

          have [simp]: "set IB' \<inter> set ICA' = {}"
            by (metis ICA'_def append_is_Nil_conv empty_inter filter_append inter_filter newvars_old_distinct_a set_inter)

          have a: "TVs ICA = TVs ICA'"
            by (simp add: ICA_def ICA'_def)

          have [simp]: "length ICA' = length ICA"
            by (metis length_TVs a)


          have b: "Subst (IB' @ IA @ ICA') (IB @ IA @ ICA) IA = IA"
            apply (subst Subst_not_in_a)
            apply (simp_all)
            apply (subst Subst_not_in)
            by (simp_all add: Int_commute)
 
          have c: "Subst (IB' @ IA @ ICA') (IB @ IA @ ICA) IB' = IB"
            apply (subst Subst_not_in)
            apply simp_all
            using \<open>set IB' \<inter> set IA = {}\<close> \<open>set IB' \<inter> set ICA' = {}\<close> by blast

          have d: "Subst (IB' @ IA @ ICA') (IB @ IA @ ICA) ICA' = ICA"
            apply (cut_tac x="IB' @ IA " and x'="ICA'" and y="IB @ IA" and y'="ICA" and z="ICA'" in Subst_not_in_a)
            apply simp_all
            using \<open>set IB' \<inter> set ICA' = {}\<close> \<open>set IA \<inter> set ICA' = {}\<close> by blast

          have [simp]: "Subst (IB' @ IA @ ICA') (IB @ IA @ ICA) (IA @ IB' @ ICA') = IA @ IB @ ICA"
            by (simp add: Subst_append b c d)

          have [simp]: "set OA \<inter> set ICA' = {}"
            by (metis ICA'_def Int_commute bot_eq_sup_iff inf_sup_distrib1 newvars_old_distinct_a set_append)

          have [simp]: "set OA \<inter> set ICA = {}"
            by (simp add: ICA_def set_diff)

          have [simp]: "set IB' \<inter> set OA = {}"
            using \<open>set OA \<inter> set IB' = {}\<close> by blast

          have [simp]: "set IC \<subseteq> set OA \<union> set ICA"
            by (simp add: ICA_def set_diff)

          have [simp]: "set ICA' \<inter> set ICA = {}"
            by (metis newvars_old_distinct_a ICA'_def Int_commute bot_eq_sup_iff inf_sup_distrib2 set_append)

          have e: "Subst ICA' ICA (OA @ IB' @ ICA') = OA @ IB' @ ICA"
            by (simp add: Subst_append)

          have f: "Subst ICA' ICA (IB' @ OA @ ICA') = IB' @ OA @ ICA"
            by (simp add: Subst_append)

          have [simp]: "set OA \<inter> set (IB \<oplus> ICA) = {}"
            apply (simp add: set_addvars)
            by (simp add: OA_def IB_def Out_out)

          have g: "IB \<oplus> ICA = (IB \<oplus> IC \<ominus> OA)"
            apply (simp add: ICA_def addvars_def union_diff)
            apply (subgoal_tac "set IB \<inter> set OA = {}")
            apply (simp add: diff_disjoint diff_sym)
            by (simp add: OA_def IB_def Out_out)


          have A: "[In B \<oplus> (In A \<oplus> (In C \<ominus> Out A)) \<leadsto> In B @ (In A \<oplus> (In C \<ominus> Out A))] oo
                      Trs B \<parallel> ([In A \<oplus> (In C \<ominus> Out A) \<leadsto> In A @ (In C \<ominus> Out A)] oo Trs A \<parallel> [In C \<ominus> Out A \<leadsto> In C \<ominus> Out A] oo [out A # (In C \<ominus> Out A) \<leadsto> In C] oo Trs C) = 
                   [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo [OA @ IB' @ ICA \<leadsto> IB' @ IC] oo Trs B \<parallel> Trs C"
            proof-
              have "[In B \<oplus> (In A \<oplus> (In C \<ominus> Out A)) \<leadsto> In B @ (In A \<oplus> (In C \<ominus> Out A))] oo
                    Trs B \<parallel> ([In A \<oplus> (In C \<ominus> Out A) \<leadsto> In A @ (In C \<ominus> Out A)] oo Trs A \<parallel> [In C \<ominus> Out A \<leadsto> In C \<ominus> Out A] oo [out A # (In C \<ominus> Out A) \<leadsto> In C] oo Trs C) = 
                    [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    Trs B \<parallel> ([IA \<oplus> ICA \<leadsto> IA @ ICA] oo Trs A \<parallel> [ICA \<leadsto> ICA] oo [OA @ ICA \<leadsto> IC] oo Trs C)" (is "?lhs = ?T")
                by (simp add: IA_def IB_def IC_def ICA_def OA_def Out_out)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB \<leadsto> IB] \<parallel> ([IA \<oplus> ICA \<leadsto> IA @ ICA] oo Trs A \<parallel> [ICA \<leadsto> ICA] oo [OA @ ICA \<leadsto> IC]) oo Trs B \<parallel> Trs C)"
                by (simp add: comp_parallel_distrib  )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    (([IB \<leadsto> IB] \<parallel> ([IA \<oplus> ICA \<leadsto> IA @ ICA] oo Trs A \<parallel> [ICA \<leadsto> ICA]) oo [IB \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC]) oo Trs B \<parallel> Trs C)"
                by (subst(2) comp_parallel_distrib, simp_all )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB \<leadsto> IB] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo [IB \<leadsto> IB] \<parallel> (Trs A \<parallel> [ICA \<leadsto> ICA]) oo [IB \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
                by (simp add: comp_parallel_distrib  )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB \<leadsto> IB] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo ([IB \<leadsto> IB] \<parallel> Trs A) \<parallel> [ICA \<leadsto> ICA] oo [IB \<leadsto> IB] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
                by (simp add: par_assoc)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB' \<leadsto> IB'] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo ([IB' \<leadsto> IB'] \<parallel> Trs A) \<parallel> [ICA \<leadsto> ICA] oo [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
                by (simp add: IB'_def distinct_id)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB' \<leadsto> IB'] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo 
                    ([IB' @ IA \<leadsto> IA @ IB'] oo Trs A \<parallel> [IB' \<leadsto> IB'] oo [OA @ IB' \<leadsto> IB' @ OA]) \<parallel> [ICA \<leadsto> ICA] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
                apply (cut_tac S="[IB' \<leadsto> IB']" and T ="Trs A" and x="IB'" and y="IA" and u="OA" and v="IB'" in switch_par)
                by simp_all
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB' \<leadsto> IB'] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo 
                    (([IB' @ IA \<leadsto> IA @ IB'] oo Trs A \<parallel> [IB' \<leadsto> IB']) \<parallel> [ICA \<leadsto> ICA]  oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA \<leadsto> ICA]) oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
                by (subst(2) comp_parallel_distrib, simp_all add:   switch_comp)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    ([IB' \<leadsto> IB'] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo 
                    (([IB' @ IA \<leadsto> IA @ IB'] \<parallel> [ICA \<leadsto> ICA] oo Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA \<leadsto> ICA]) oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA \<leadsto> ICA]) oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C)"
                by (subst(2) comp_parallel_distrib, simp_all)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    [IB' \<leadsto> IB'] \<parallel> [IA \<oplus> ICA \<leadsto> IA @ ICA] oo 
                    [IB' @ IA \<leadsto> IA @ IB'] \<parallel> [ICA \<leadsto> ICA] oo Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA \<leadsto> ICA] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA \<leadsto> ICA] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: comp_assoc [THEN sym]  )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @ (IA \<oplus> ICA)] oo
                    [IB' @ (IA \<oplus> ICA) \<leadsto> IB' @  (IA @ ICA)] oo 
                    [IB' @ IA \<leadsto> IA @ IB'] \<parallel> [ICA \<leadsto> ICA] oo Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA \<leadsto> ICA] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA \<leadsto> ICA] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: par_switch set_addvars)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @  (IA @ ICA)] oo 
                    [IB' @ IA \<leadsto> IA @ IB'] \<parallel> [ICA \<leadsto> ICA] oo Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA \<leadsto> ICA] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA \<leadsto> ICA] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: switch_comp_subst set_addvars)
    
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @  (IA @ ICA)] oo 
                    [IB' @ IA \<leadsto> IA @ IB'] \<parallel> [ICA' \<leadsto> ICA'] oo Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA' \<leadsto> ICA'] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA' \<leadsto> ICA'] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: ICA'_def switch_newvars)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IB @  (IA @ ICA)] oo 
                    [IB' @ IA @ ICA'\<leadsto> IA @ IB' @ ICA'] oo Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA' \<leadsto> ICA'] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA' \<leadsto> ICA'] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: par_switch)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' \<leadsto> IB'] \<parallel> [ICA' \<leadsto> ICA'] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA' \<leadsto> ICA'] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                apply (subst switch_comp_subst, simp_all add: a)
                by (auto simp add: set_addvars set_diff)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo [OA @ IB' \<leadsto> IB' @ OA] \<parallel> [ICA' \<leadsto> ICA'] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: par_assoc par_switch)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo [OA @ IB'@ ICA' \<leadsto> IB' @ OA @ ICA'] oo 
                    [IB' \<leadsto> IB'] \<parallel> [OA @ ICA \<leadsto> IC] oo Trs B \<parallel> Trs C"
                by (simp add: par_switch)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo [OA @ IB'@ ICA' \<leadsto> IB' @ OA @ ICA'] oo 
                    [IB' @ OA @ ICA \<leadsto> IB' @ IC] oo Trs B \<parallel> Trs C"
                by (subst par_switch, simp_all)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo 
                    ([OA @ IB'@ ICA' \<leadsto> IB' @ OA @ ICA'] oo [IB' @ OA @ ICA \<leadsto> IB' @ IC]) oo 
                    Trs B \<parallel> Trs C"
                by (simp add: comp_assoc a  )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo 
                    ([OA @ IB'@ ICA \<leadsto> IB' @ OA @ ICA] oo [IB' @ OA @ ICA \<leadsto> IB' @ IC]) oo 
                    Trs B \<parallel> Trs C"
                apply (cut_tac x="OA @ IB'@ ICA'" and y="IB' @ OA @ ICA'" and u="ICA'" and v="ICA" in Subst_switch_more_general)
                apply simp_all
                using \<open>set IB' \<inter> set ICA = {}\<close> \<open>set ICA' \<inter> set ICA = {}\<close> \<open>set OA \<inter> set ICA = {}\<close> apply blast
                apply blast
                by (simp_all add: a e f)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo 
                    Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo 
                    [OA @ IB' @ ICA \<leadsto> IB' @ IC] oo 
                    Trs B \<parallel> Trs C"
                apply (subst switch_comp, simp_all)
                using perm_tp perm_union_left apply fastforce
                by (auto simp add: IC_def ICA_def set_addvars set_diff)
              finally show ?thesis
                by simp
            qed

          have [simp]: "distinct (IA \<oplus> (IB \<oplus> ICA))"
            by (simp )

          have [simp]: "perm (IB \<oplus> (IA \<oplus> ICA)) (IA \<oplus> (IB \<oplus> ICA))"
            apply (subst set_perm)
            apply simp_all
            apply (simp add: set_addvars)
            by blast

          have [simp]: "distinct (IB \<oplus> ICA)"
            by (simp )

          have [simp]: "IC \<otimes> OA = OA"
            apply (subgoal_tac "distinct IC")
            apply (simp add: IC_def OA_def Out_out)
            apply (subgoal_tac "out A \<in> set (In C)")
            apply (simp add: inter_subset_l1)
            by simp_all            

          have [simp]: "IB \<otimes> OA = []"
            apply (simp add: IB_def OA_def Out_out)
            apply (subgoal_tac "out A \<notin> set (In B)")
            apply (simp add: empty_inter)
            by simp            

          have [simp]: "perm (OA @ (IB \<oplus> ICA)) (IB \<oplus> IC)"
            apply (simp add: ICA_def addvars_def diff_sym)
            apply (subgoal_tac "perm (OA @ IB @ (IC \<ominus> IB \<ominus> OA)) (IB @ OA @ (IC \<ominus> IB \<ominus> OA))")
            apply (subgoal_tac "perm (OA @ (IC \<ominus> IB \<ominus> OA)) (IC \<ominus> IB)")
            using perm_trans perm_union_right apply blast
            apply (subgoal_tac "OA = ((IC \<ominus> IB) \<otimes> OA)")
            apply (metis mset_inter_diff perm_def union_code)
            apply (simp add: inter_diff_distrib diff_emptyset)  
            using perm_tp perm_union_left by fastforce
            

          have B: "[In B \<oplus> (In A \<oplus> (In C \<ominus> Out A)) \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> Out A)] oo
                ([In A \<oplus> (In B \<oplus> In C \<ominus> Out A) \<leadsto> In A @ (In B \<oplus> In C \<ominus> Out A)] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> Out A \<leadsto> In B \<oplus> In C \<ominus> Out A] oo [out A # (In B \<oplus> In C \<ominus> Out A) \<leadsto> In B \<oplus> In C] oo
                ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C)) 
                = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo
                Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo 
                [OA @ (IB \<oplus> ICA) \<leadsto> IB @ IC]
                oo Trs B \<parallel> Trs C"
            proof-        
              have "[In B \<oplus> (In A \<oplus> (In C \<ominus> Out A)) \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> Out A)] oo
                    ([In A \<oplus> (In B \<oplus> In C \<ominus> Out A) \<leadsto> In A @ (In B \<oplus> In C \<ominus> Out A)] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> Out A \<leadsto> In B \<oplus> In C \<ominus> Out A] oo [out A # (In B \<oplus> In C \<ominus> Out A) \<leadsto> In B \<oplus> In C] oo
                    ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C)) =
                    [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA \<oplus> (IB \<oplus> ICA)] oo
                    ([IA \<oplus> (IB \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> (IB \<oplus> IC)] oo
                    ([IB \<oplus> IC \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C))"
                apply (simp only: g)
                by (simp add: IA_def IB_def ICA_def IC_def OA_def Out_out)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA \<oplus> (IB \<oplus> ICA)] oo
                    [IA \<oplus> (IB \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> (IB \<oplus> IC)] oo
                    [IB \<oplus> IC \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C"
                by (simp add: comp_assoc[THEN sym]  )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo
                    Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> (IB \<oplus> IC)] oo
                    [IB \<oplus> IC \<leadsto> IB @ IC] oo Trs B \<parallel> Trs C"
                by (subst switch_comp, simp_all)
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo
                    Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo 
                    ([OA @ (IB \<oplus> ICA) \<leadsto> (IB \<oplus> IC)] oo [IB \<oplus> IC \<leadsto> IB @ IC])
                    oo Trs B \<parallel> Trs C"
                by (simp add: comp_assoc  )
              also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo
                    Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo 
                    [OA @ (IB \<oplus> ICA) \<leadsto> IB @ IC]
                    oo Trs B \<parallel> Trs C"
                by (subst switch_comp, simp_all)
              finally show ?thesis
                by simp
            qed

          have h: "Subst (OA @ IB' @ ICA) (OA @ IB @ ICA) IB' = IB"
            apply (subst Subst_not_in_a, simp_all)
            by (subst Subst_not_in, simp_all add: Int_commute)

          have i: "Subst (OA @ IB' @ ICA) (OA @ IB @ ICA) IC = IC"
            apply (subst Subst_cancel_right, simp_all)
            apply (subst Subst_not_in_a, simp_all)
            apply (metis ICA_def \<open>set IB' \<inter> set ICA = {}\<close> \<open>set IB' \<inter> set OA = {}\<close> inter_diff_empty set_inter)
            by (simp add: Subst_eq)
            

          have [simp]: "Subst (OA @ IB' @ ICA) (OA @ IB @ ICA) (IB' @ IC) = IB @ IC"
            by (simp add: Subst_append h i)

          have C: "[OA @ (IB \<oplus> ICA) \<leadsto> IB @ IC] = [OA @ (IB \<oplus> ICA) \<leadsto> OA @ IB @ ICA] oo [OA @ IB' @ ICA \<leadsto> IB' @ IC]"
            apply (subst switch_comp_subst, simp_all)
            by (auto simp add: set_addvars set_diff IC_def ICA_def)

          from this have D: "[IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> IB @ IC]
            = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> OA @ IB @ ICA] oo [OA @ IB' @ ICA \<leadsto> IB' @ IC]"
            apply simp
            by (simp add: comp_assoc  )

          have [simp]: "set OA \<inter> set IB = {}"
            by (simp add: OA_def IB_def Out_out)

          def IA' \<equiv> "newvars (IB \<oplus> ICA) (TVs IA)"

          have [simp]: "distinct IA'"
            by (simp add: IA'_def)

          have [simp]: "TI (Trs A) = TVs IA'"
            by (simp add: IA'_def)

          have [simp]: "set IA' \<inter> set (IB \<oplus> ICA) = {}"
            by (simp only: IA'_def newvars_old_distinct)

          have [simp]: "length IA' = length IA"
            by (metis TVs_length_eq \<open>TI (Trs A) = TVs IA'\<close> \<open>TVs IA = TI (Trs A)\<close>)

          have j: "Subst (IA' @ (IB \<oplus> ICA)) (IA @ (IB \<oplus> ICA)) IA' = IA"
            by (subst Subst_not_in, simp_all add: Int_commute)

          have [simp]: "set IA' \<inter> set IB = {}"
            by (metis UnCI \<open>set IA' \<inter> set (IB \<oplus> ICA) = {}\<close> disjoint_iff_not_equal set_addvars)

          have [simp]: "set IA' \<inter> set ICA = {}"
            by (metis UnCI \<open>set IA' \<inter> set (IB \<oplus> ICA) = {}\<close> disjoint_iff_not_equal set_addvars)

          have k: "Subst (IA' @ (IB \<oplus> ICA)) (IA @ (IB \<oplus> ICA)) (IB @ ICA) = IB @ ICA"
            by (simp add: Subst_not_in_a Subst_eq)

          have [simp]: " Subst (IA' @ (IB \<oplus> ICA)) (IA @ (IB \<oplus> ICA)) (IA' @ IB @ ICA) = IA @ IB @ ICA"
            apply (subst Subst_append)
            by (simp add: j k)

          have "[IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> OA @ IB @ ICA]
            = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA \<leadsto> OA] \<parallel> [IB \<oplus> ICA \<leadsto> IB @ ICA]"
            by (subst par_switch, simp_all add: set_addvars)
          also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo (Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA \<leadsto> OA] \<parallel> [IB \<oplus> ICA \<leadsto> IB @ ICA])"
            by (subst comp_assoc, simp_all add:  )
          also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB @ ICA]"
            by (subst comp_parallel_distrib, simp_all)
          also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo ([IA' \<leadsto> IA'] oo Trs A) \<parallel> ([IB \<oplus> ICA \<leadsto> IB @ ICA] oo [IB' @ ICA' \<leadsto> IB' @ ICA'])"
            apply (subst comp_id_switch, simp_all)
            apply (subst comp_switch_id, simp_all)
            by (simp add: a)
          also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo ([IA' @ (IB \<oplus> ICA) \<leadsto> IA' @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'])"
            apply (subst comp_parallel_distrib [THEN sym], simp_all add: a)
            by (subst par_switch, simp_all)
         also have "... = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo [IA' @ (IB \<oplus> ICA) \<leadsto> IA' @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA']"
           by (subst comp_assoc, simp_all add: comp_assoc  a)
         also have "... =  [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA']"
          apply (subst switch_comp_subst, simp_all)
          by (auto simp add: set_addvars set_diff)
            

         finally have E: "[IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] 
              = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> OA @ IB @ ICA]"
           by simp

          show "[In B \<oplus> (In A \<oplus> (In C \<ominus> Out A)) \<leadsto> In B @ (In A \<oplus> (In C \<ominus> Out A))] oo
              Trs B \<parallel> ([In A \<oplus> (In C \<ominus> Out A) \<leadsto> In A @ (In C \<ominus> Out A)] oo Trs A \<parallel> [In C \<ominus> Out A \<leadsto> In C \<ominus> Out A] oo [out A # (In C \<ominus> Out A) \<leadsto> In C] oo Trs C) =
              [In B \<oplus> (In A \<oplus> (In C \<ominus> Out A)) \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> Out A)] oo
              ([In A \<oplus> (In B \<oplus> In C \<ominus> Out A) \<leadsto> In A @ (In B \<oplus> In C \<ominus> Out A)] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> Out A \<leadsto> In B \<oplus> In C \<ominus> Out A] oo [out A # (In B \<oplus> In C \<ominus> Out A) \<leadsto> In B \<oplus> In C] oo
              ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C))"
            apply (simp add: A B)
            apply (subgoal_tac " [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] oo [OA @ IB' @ ICA \<leadsto> IB' @ IC] = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> IB @ IC]")
            apply (simp_all)
            apply (subst D)
            apply (subgoal_tac " [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ IB @ ICA] oo Trs A \<parallel> [IB' @ ICA' \<leadsto> IB' @ ICA'] = [IB \<oplus> (IA \<oplus> ICA) \<leadsto> IA @ (IB \<oplus> ICA)] oo Trs A \<parallel> [IB \<oplus> ICA \<leadsto> IB \<oplus> ICA] oo [OA @ (IB \<oplus> ICA) \<leadsto> OA @ IB @ ICA]")
            apply simp_all
            by (simp add: E)
        qed

section{*Simplification rules*}

      thm in_equiv_CompA_Parallel_c

      thm in_equiv_Parallel

      lemma perm_append: "perm x x' \<Longrightarrow> perm y y' \<Longrightarrow> perm (x @ y) (x' @ y')"
        by (simp add: perm_def)



      lemma "x' = y @ a # y' \<Longrightarrow> perm x (y @ y') \<Longrightarrow> perm (a # x) x'"
        by (simp add: perm_def)


      lemma perm_refl[simp]: "perm x x"
        by (simp add: perm_def)

      lemma perm_diff_eq[simp]: "perm y y' \<Longrightarrow> (x \<ominus> y) = (x \<ominus> y')"
        apply (drule perm_set_eq)
        by (induction x, auto)


      lemmas distinct_addvars distinct_diff

      lemma type_ok_distinct: assumes A: "type_ok A" shows [simp]: "distinct (In A)" and [simp]: "distinct (Out A)" and [simp]: "TI (Trs A) = TVs (In A)" and [simp]: "TO (Trs A) = TVs (Out A)"
        using A by (simp_all add: type_ok_def)

      lemma [simp]: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False"
        by auto
      lemma [simp]: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
        by auto

      lemma [simp]: "B \<inter> A = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
        by auto
      lemma [simp]: "B \<inter> A = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False"
        by auto

      lemma distinct_perm_switch: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm (x \<oplus> y) (y \<oplus> x)"
        apply (simp add: addvars_def)
        by (rule set_perm, simp_all add: set_diff, auto)

      thm Subst_not_in

      declare Subst_not_in_a  [simp]
      declare Subst_not_in  [simp]

      lemma [simp]: "set x' \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> TVs x' = TVs y' \<Longrightarrow> Subst (x @ x') (y @ y') z = Subst x y z"
        by (metis Subst_not_in length_TVs)

      lemma [simp]: "set x \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> TVs x' = TVs y' \<Longrightarrow> Subst (x @ x') (y @ y') z = Subst x' y' z"
        by (metis Subst_not_in_a length_TVs)

      lemma [simp]: "set x \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> Subst x y z = z"
        by (metis Subst_inex length_TVs)

      lemma [simp]: "distinct x \<Longrightarrow> TVs x = TVs y \<Longrightarrow> Subst x y x = y"
        by (metis Subst_all length_TVs)

(*
      declare Subst_all [simp]
*)

      lemma "TVs x = TVs y \<Longrightarrow> length x = length y"
        by (metis length_TVs)

        thm length_TVs

(*end simplification rules*)
(*
      lemma in_equiv_switch_Parallel: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (Out A) \<inter> set (Out B) = {}  \<Longrightarrow> 
        in_equiv (A ||| B) ((B ||| A) ;; \<lparr>In = Out B @ Out A, Out = Out A @ Out B, Trs = [Out B @ Out A \<leadsto> Out A @ Out B]\<rparr>)"
 *)



      lemma in_equiv_switch_Parallel: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (Out A) \<inter> set (Out B) = {}  \<Longrightarrow> 
        in_equiv (A ||| B) ((B ||| A) ;; [[ Out B @ Out A \<leadsto> Out A @ Out B]])"
        apply (simp add: in_equiv_def Let_def Parallel_def Comp_def VarSwitch_def Var_def diff_inter_left diff_inter_right diff_eq par_empty_left par_empty_right)
        apply safe
        apply (metis addvars_def perm_switch perm_tp perm_trans type_ok_def)
        proof -
          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"

          assume [simp]: "set (Out A) \<inter> set (Out B) = {}"
          from this have [simp]: "set (Out B) \<inter> set (Out A) = {}"
            by blast

          have [simp]: "perm (In A \<oplus> In B) (In B \<oplus> In A)"
            by (rule distinct_perm_switch, simp_all)

         from paralle_switch obtain x y u v where
            B: "distinct (x @ y)" and C: "distinct (u @ v)" and [simp]: "TVs x = TI (Trs B)" and [simp]: "TVs u = TO (Trs B)" and [simp]: "TVs y = TI (Trs A)" 
            and [simp]: "TVs v = TO (Trs A)" and A: "Trs B \<parallel> Trs A = [x @ y \<leadsto> y @ x] oo (Trs A \<parallel> Trs B) oo [v @ u \<leadsto> u @ v]"
            by blast

          from C have [simp]: "distinct u" and [simp]: "distinct v" and [simp]: "set u \<inter> set v = {}" and [simp]: "set v \<inter> set u = {}"
            by auto

          from B have [simp]: "distinct x" and [simp]: "distinct y" and [simp]: "set x \<inter> set y = {}" and [simp]: "set y \<inter> set x = {}"
            by auto

          have [simp]: "Subst (x @ y) (In B @ In A) (y @ x) = In A @ In B"
            by (simp add: Subst_append)

          have [simp]: "Subst (Out B @ Out A) (u @ v) (Out A @ Out B) = v @ u"
            by (simp add: Subst_append)


            thm comp_id_left
          have "[In A \<oplus> In B \<leadsto> In B \<oplus> In A] oo ([In B \<oplus> In A \<leadsto> In B \<oplus> In A] oo ([In B \<oplus> In A \<leadsto> In B @ In A] oo Trs B \<parallel> Trs A) oo [Out B @ Out A \<leadsto> Out B @ Out A] oo [Out B @ Out A \<leadsto> Out A @ Out B])
            = [In A \<oplus> In B \<leadsto> In B \<oplus> In A] oo ([In B \<oplus> In A \<leadsto> In B @ In A] oo Trs B \<parallel> Trs A oo [Out B @ Out A \<leadsto> Out B @ Out A] oo [Out B @ Out A \<leadsto> Out A @ Out B])"
          by (simp add: distinct_id)
          also have "... = ([In A \<oplus> In B \<leadsto> In B \<oplus> In A] oo [In B \<oplus> In A \<leadsto> In B @ In A]) oo Trs B \<parallel> Trs A oo ([Out B @ Out A \<leadsto> Out B @ Out A] oo [Out B @ Out A \<leadsto> Out A @ Out B])"
            by (simp add: comp_assoc)

          also have "... = [In A \<oplus> In B \<leadsto> In B @ In A] oo Trs B \<parallel> Trs A oo [Out B @ Out A  \<leadsto> Out A @ Out B]"
            apply (subst switch_comp)
            by (auto simp add: set_addvars set_diff)

          also have "... = [In A \<oplus> In B \<leadsto> In B @ In A] oo ([x @ y \<leadsto> y @ x] oo (Trs A \<parallel> Trs B) oo [v @ u \<leadsto> u @ v]) oo [Out B @ Out A  \<leadsto> Out A @ Out B]"
            by (simp add: A)
          also have "... = ([In A \<oplus> In B \<leadsto> In B @ In A] oo [x @ y \<leadsto> y @ x]) oo Trs A \<parallel> Trs B oo ([v @ u \<leadsto> u @ v] oo [Out B @ Out A  \<leadsto> Out A @ Out B])"
            using B C by (simp add: comp_assoc)

          also have "... = [In A \<oplus> In B \<leadsto> In A @ In B] oo Trs A \<parallel> Trs B"
            using B C by (simp add: switch_comp_subst distinct_id set_addvars set_diff)

          finally show "[In A \<oplus> In B \<leadsto> In A @ In B] oo Trs A \<parallel> Trs B 
                      = [In A \<oplus> In B \<leadsto> In B \<oplus> In A] oo ([In B \<oplus> In A \<leadsto> In B @ In A] oo Trs B \<parallel> Trs A oo [Out B @ Out A \<leadsto> Out B @ Out A] oo [Out B @ Out A \<leadsto> Out A @ Out B])"
          by simp
       qed

      lemma in_out_equiv_Parallel: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> set (Out A) \<inter> set (Out B) = {}  \<Longrightarrow>  in_out_equiv (A ||| B) (B ||| A)"
        apply (frule in_equiv_switch_Parallel, simp_all)
        apply (simp add: in_equiv_def in_out_equiv_def Parallel_def VarSwitch_def Let_def Comp_def Var_def par_empty_left par_empty_right, safe)
        using distinct_perm_switch type_ok_distinct(1) apply blast
        using perm_tp apply blast
        apply (unfold type_ok_def)
        apply (simp add: comp_assoc)
        by (subst switch_comp, auto)


      declare Subst_eq [simp]

      lemma assumes "in_equiv A A'" shows [simp]: "perm (In A) (In A')" 
        using assms in_equiv_def by blast

      lemma Subst_cancel_left_type: "set x \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> Subst (x @ z) (y @ z) w = Subst x y w"
        by (metis Subst_cancel_left length_TVs)

      lemma diff_eq_set_right: "set y = set z \<Longrightarrow> (x \<ominus> y) = (x \<ominus> z)"
        by (metis diff_inter_left list_inter_set)


      lemma [simp]: "set (y \<ominus> x) \<inter> set x = {}"
        by (auto simp add: set_diff)

      lemma in_equiv_Comp: "type_ok A' \<Longrightarrow> type_ok B' \<Longrightarrow> in_equiv A A' \<Longrightarrow> in_equiv B B' \<Longrightarrow> in_equiv (A ;; B) (A' ;; B')"
        proof -
          assume [simp]: "type_ok A'"
          assume [simp]: "type_ok B'"
          assume [simp]: "in_equiv A A'"
          assume [simp]: "in_equiv B B'"

          have [simp]: "type_ok A"
            using \<open>in_equiv A A'\<close> \<open>type_ok A'\<close> in_equiv_type_ok by blast
          have [simp]: "type_ok B"
            using \<open>in_equiv B B'\<close> \<open>type_ok B'\<close> in_equiv_type_ok by blast

          have [simp]: "Out A = Out A'"
            using \<open>in_equiv A A'\<close> in_equiv_def by blast

          have [simp]: "Out B = Out B'"
            using \<open>in_equiv B B'\<close> in_equiv_def by blast

          from \<open>in_equiv A A'\<close> have [simp]: "Trs A = [In A \<leadsto> In A'] oo Trs A'"
            by (simp add: in_equiv_def)

          from \<open>in_equiv B B'\<close> have [simp]: "Trs B = [In B \<leadsto> In B'] oo Trs B'"
            by (simp add: in_equiv_def)

          have [simp]: "set (In A') = set (In A)"
            using \<open>in_equiv A A'\<close> in_equiv_def perm_set_eq by blast
    
          have [simp]: "set (In B') = set (In B)"
            using \<open>in_equiv B B'\<close> in_equiv_def perm_set_eq by blast

          have [simp]: "(Out A' \<ominus> In B') = (Out A' \<ominus> In B)"
            by (rule diff_eq_set_right, simp)

          def v \<equiv> "newvars (In A @ In B) (TVs (Out A'))"

          have [simp]: "distinct v"
            by (simp add: v_def)

          have U: "set v \<inter> set (In A @ In B) = {}"
            using newvars_old_distinct v_def by blast



        have [simp]:" set (In A \<oplus> (In B \<ominus> Out A')) \<inter> set v = {}"
          using U by (unfold set_addvars set_diff, auto)

        have [simp]:" set v \<inter> set (In A \<oplus> (In B \<ominus> Out A')) = {}"
          using U by (unfold set_addvars set_diff, auto)
          
          from U have [simp]: "set v \<inter> set (In A) = {}"
            by simp
          from U have [simp]: "set v \<inter> set (In B) = {}"
            by simp
          
        have [simp]: "TVs v = TVs (Out A')"
          by (simp add: v_def)


        have [simp]:"set (In A') \<subseteq> set (In A \<oplus> (In B \<ominus> Out A'))"
          by (simp add: set_diff set_addvars)

        have [simp]:"set (In B \<ominus> Out A') \<subseteq> set (In A \<oplus> (In B \<ominus> Out A'))"
          by (simp add: set_diff set_addvars)

        have [simp]:"set (In B' \<ominus> Out A') \<subseteq> set (In A \<oplus> (In B \<ominus> Out A'))"
          by (simp add: set_diff set_addvars)


        have A: "([In A \<leadsto> In A'] oo Trs A') \<parallel> [In B \<ominus> Out A' \<leadsto> In B \<ominus> Out A'] = [In A \<leadsto> In A'] \<parallel> [In B \<ominus> Out A' \<leadsto> In B \<ominus> Out A'] oo Trs A' \<parallel> [In B \<ominus> Out A' \<leadsto> In B \<ominus> Out A']"
          by (simp add: comp_parallel_distrib)

        have [simp]: "[Out A' \<ominus> In B \<leadsto> Out A' \<ominus> In B] \<parallel> ([In B \<leadsto> In B'] oo Trs B') = [(Out A' \<ominus> In B) \<leadsto> (Out A' \<ominus> In B)] \<parallel> [In B \<leadsto> In B'] oo [Out A' \<ominus> In B \<leadsto> Out A' \<ominus> In B] \<parallel> Trs B'"
          by (simp add: comp_parallel_distrib)

        have [simp]: "... = [(Out A' \<ominus> In B) @ In B \<leadsto> (Out A' \<ominus> In B) @ In B'] oo [Out A' \<ominus> In B \<leadsto> Out A' \<ominus> In B] \<parallel> Trs B'"
          by (subst par_switch, simp_all)

        have "[In A \<oplus> (In B \<ominus> Out A') \<leadsto> In A @ (In B \<ominus> Out A')] oo ([In A \<leadsto> In A'] oo Trs A') \<parallel> [In B \<ominus> Out A' \<leadsto> In B \<ominus> Out A'] 
              oo ([Out A' @ (In B \<ominus> Out A') \<leadsto> (Out A' \<ominus> In B) @ In B] oo [(Out A' \<ominus> In B) @ In B \<leadsto> (Out A' \<ominus> In B) @ In B'])
                =
              [In A \<oplus> (In B \<ominus> Out A') \<leadsto> In A' \<oplus> (In B' \<ominus> Out A')] oo
              [In A' \<oplus> (In B' \<ominus> Out A') \<leadsto> In A' @ (In B' \<ominus> Out A')] oo Trs A' \<parallel> [In B' \<ominus> Out A' \<leadsto> In B' \<ominus> Out A'] 
              oo [Out A' @ (In B' \<ominus> Out A') \<leadsto> (Out A' \<ominus> In B) @ In B']"

          apply (subst switch_comp_a, simp_all)
          apply (auto simp add: set_diff) [1]
          apply (subst A, simp add: comp_assoc [THEN sym])
          apply (subst switch_par_comp_Subst, simp_all)
          apply (subst switch_comp, simp_all)
          apply (simp add: set_diff set_addvars)
          apply (rule_tac v = v in par_switch_eq_dist, simp_all)
          apply (subst switch_comp_subst, simp_all)
          apply (auto simp add: set_diff set_addvars)
          apply (subst switch_comp_subst, simp_all)
          apply (auto simp add: set_diff set_addvars)
          by (simp add: Subst_append Subst_cancel_left_type)

         thm par_switch_eq_dist
         from this show "in_equiv (A ;; B) (A' ;; B')"
          apply (simp add: in_equiv_def Comp_def Let_def Var_def diff_inter_left diff_inter_right, simp)
          by (simp add: comp_assoc [THEN sym])
      qed


      lemma "type_ok A' \<Longrightarrow> type_ok B' \<Longrightarrow> in_equiv A A' \<Longrightarrow> in_equiv B B' \<Longrightarrow> in_equiv (CompA A  B) (CompA A' B')"
        apply (simp add: CompA_def, safe)
        apply (rule in_equiv_Comp, simp_all)
        apply (metis in_equiv_def out_def perm_set_eq)
        by (metis in_equiv_def out_def perm_set_eq)

      thm in_equiv_tran

      thm in_equiv_CompA_Parallel_c

      lemma comp_parallel_distrib_a: "TO A = TI B \<Longrightarrow> (A oo B) \<parallel> C = (A \<parallel> (ID (TI C))) oo (B \<parallel> C)"
        by (subst comp_parallel_distrib, simp_all)

      lemma comp_parallel_distrib_b: "TO A = TI B \<Longrightarrow> C \<parallel> (A oo B) = ((ID (TI C)) \<parallel> A) oo (C \<parallel> B)"
        by (subst comp_parallel_distrib, simp_all)


      thm switch_comp_subst

      lemma CCC_d: "distinct x \<Longrightarrow> distinct y' \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set u \<subseteq> set y' \<Longrightarrow> TVs y = TVs y' \<Longrightarrow> 
        TVs z = ts \<Longrightarrow> [x \<leadsto> y @ z] oo [y' \<leadsto> u] \<parallel> (ID ts) = [x \<leadsto> Subst y' y u @ z]"
        proof -
        assume [simp]: "distinct x"
        assume [simp]: "distinct y'"
        assume [simp]: "set y \<subseteq> set x"
        assume [simp]: "set z \<subseteq> set x"
        assume [simp]: "set u \<subseteq> set y'"
        assume [simp]: "TVs y = TVs y'"
        assume [simp]: "TVs z = ts"
        def z' \<equiv> "newvars y' (TVs z)"

        have [simp]: "set y' \<inter> set z' = {}"
          by (simp add: z'_def)
        have [simp]: "set z' \<inter> set y' = {}"
          by (simp add: z'_def)
        have [simp]: "set u \<inter> set z' = {}"
          using \<open>set u \<subseteq> set y'\<close> \<open>set y' \<inter> set z' = {}\<close> by blast
        have [simp]: "set z' \<inter> set u = {}"
          using \<open>set u \<subseteq> set y'\<close> \<open>set y' \<inter> set z' = {}\<close> by blast
        have [simp]: "TVs z' = TVs z"
          by (simp add: z'_def)
        have [simp]: "distinct z'"
          by (simp add: z'_def)

        have " [x \<leadsto> y @ z] oo [y' \<leadsto> u] \<parallel> (ID ts) =  [x \<leadsto> y @ z] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> z']"
          by (subst distinct_id, simp_all add: z'_def)
        also have "... =  [x \<leadsto> y @ z] oo [y' @ z' \<leadsto> u @ z']"
          by (subst par_switch, simp_all add: z'_def)
        also have "... = [x \<leadsto> Subst y' y u @ z]"
          apply (subst switch_comp_subst, simp_all add: Subst_append)
          by (simp add: le_supI1)

        finally show ?thesis
          by simp
     qed

      lemma CCC_e: "distinct x \<Longrightarrow> distinct y' \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set u \<subseteq> set y' \<Longrightarrow> TVs y = TVs y' \<Longrightarrow> 
        TVs z = ts \<Longrightarrow> [x \<leadsto> z @ y] oo (ID ts) \<parallel> [y' \<leadsto> u] = [x \<leadsto> z @ Subst y' y u]"
        proof -
        assume [simp]: "distinct x"
        assume [simp]: "distinct y'"
        assume [simp]: "set y \<subseteq> set x"
        assume [simp]: "set z \<subseteq> set x"
        assume [simp]: "set u \<subseteq> set y'"
        assume [simp]: "TVs y = TVs y'"
        assume [simp]: "TVs z = ts"
        def z' \<equiv> "newvars y' (TVs z)"

        have [simp]: "set y' \<inter> set z' = {}"
          by (simp add: z'_def)
        have [simp]: "set z' \<inter> set y' = {}"
          by (simp add: z'_def)
        have [simp]: "set u \<inter> set z' = {}"
          using \<open>set u \<subseteq> set y'\<close> \<open>set y' \<inter> set z' = {}\<close> by blast
        have [simp]: "set z' \<inter> set u = {}"
          using \<open>set u \<subseteq> set y'\<close> \<open>set y' \<inter> set z' = {}\<close> by blast
        have [simp]: "TVs z' = TVs z"
          by (simp add: z'_def)
        have [simp]: "distinct z'"
          by (simp add: z'_def)

        have " [x \<leadsto> z @ y] oo ID ts \<parallel> [y' \<leadsto> u] =  [x \<leadsto> z @ y] oo [z' \<leadsto> z'] \<parallel> [y' \<leadsto> u]"
          by (subst distinct_id, simp_all add: z'_def)
        also have "... =  [x \<leadsto> z @ y] oo [z' @ y' \<leadsto> z' @ u]"
          by (subst par_switch, simp_all add: z'_def)
        also have "... = [x \<leadsto> z @ Subst y' y u]"
          apply (subst switch_comp_subst, simp_all add: Subst_append)
          by (simp add: sup.coboundedI2)
        finally show ?thesis
          by simp
     qed


      lemma CCC_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set u \<subseteq> set y \<Longrightarrow> TVs z = ts \<Longrightarrow> [x \<leadsto> y @ z] oo [y \<leadsto> u] \<parallel> (ID ts) = [x \<leadsto> u @ z]"
        by (subst CCC_d, simp_all)
        

      lemma CCC_b: "distinct x \<Longrightarrow> distinct z \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set u \<subseteq> set z \<Longrightarrow> TVs y = ts \<Longrightarrow> [x \<leadsto> y @ z] oo  (ID ts) \<parallel> [z \<leadsto> u] = [x \<leadsto> y @ u]"
        by (subst CCC_e, simp_all)


      thm par_switch_eq_dist

      lemma in_equiv_CompA_Parallel_b: "length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> out A \<in> set (In B) 
        \<Longrightarrow>  out A \<notin> set (In C) \<Longrightarrow> in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        proof simp
          assume [simp]: "length (Out A) = Suc 0"
          assume [simp]: "out A \<notin> set (In C)"
          assume [simp]: "out A \<in> set (In B)"

          assume [simp]: "type_ok A"
          assume [simp]: "type_ok B"
          assume [simp]: "type_ok C"
        
          have [simp]: "CompA A (B ||| C) = A ;; (B ||| C)"
            apply (subgoal_tac "out A \<in> set (In (B ||| C))")
            by (simp_all add: set_addvars)

         have [simp]: "set (Out A) \<inter> set (In C) = {}"
          by (subst Out_out, simp_all)

          have [simp]: "(In C \<ominus> Out A) = In C"
            by (simp add: diff_distinct)

          have B: "(In A \<oplus> (In B \<ominus> Out A) \<oplus> In C) = (In A \<oplus> (In B \<oplus> In C \<ominus> Out A))"
            by (simp add: addvars_minus addvars_assoc)

          from B have [simp]: "perm (In A \<oplus> (In B \<ominus> Out A) \<oplus> In C) (In A \<oplus> (In B \<oplus> In C \<ominus> Out A))"
            by simp

          have A: "Out A = [out A]"
            by (subst Out_out, simp_all)

          have [simp]: "(Out A \<ominus> In B \<oplus> In C) = (Out A \<ominus> In B)"
            by (simp add: A set_addvars)

         def v \<equiv> "newvars (In A @ In B @ In C) (TVs (Out A))"

         from this have "set v \<inter> set (In A @ In B @ In C) = {}"
          using newvars_old_distinct by blast

         from this have [simp]: "set (In A \<oplus> (In B \<ominus> Out A) \<oplus> In C) \<inter> set v = {}"
           by (simp add: set_addvars set_diff, auto)

          from this have [simp]: "set v \<inter> set (In A \<oplus> (In B \<ominus> Out A) \<oplus> In C) = {}"
            by blast

         have [simp]: "distinct v"
          by (simp add: v_def)
         have [simp]: "TVs v = TVs (Out A)"
          by (simp add: v_def)


         have A: "[In A \<oplus> (In B \<ominus> Out A) \<oplus> In C \<leadsto> (In A \<oplus> (In B \<ominus> Out A)) @ In C] oo 
            [In A \<oplus> (In B \<ominus> Out A) \<leadsto> In A @ (In B \<ominus> Out A)] \<parallel> ID (TVs (In C)) oo Trs A \<parallel> [In B \<ominus> Out A \<leadsto> In B \<ominus> Out A] \<parallel> ID (TVs (In C)) oo
              [Out A @ (In B \<ominus> Out A) \<leadsto> (Out A \<ominus> In B) @ In B] \<parallel> ID (TVs (In C)) = 
            [In A \<oplus> (In B \<ominus> Out A) \<oplus> In C \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> Out A)] oo [In A \<oplus> (In B \<oplus> In C \<ominus> Out A) \<leadsto> In A @ (In B \<oplus> In C \<ominus> Out A)] 
              oo Trs A \<parallel> [In B \<oplus> In C \<ominus> Out A \<leadsto> In B \<oplus> In C \<ominus> Out A] oo
              [Out A @ (In B \<oplus> In C \<ominus> Out A) \<leadsto> (Out A \<ominus> In B) @ (In B \<oplus> In C)] oo
              ID (TVs (Out A \<ominus> In B)) \<parallel> [In B \<oplus> In C \<leadsto> In B @ In C]"
          apply (subst CCC_a, simp_all)
          apply (subst switch_comp, simp_all)
          apply (simp add: distinct_id)
          apply (simp add: par_assoc parallel_ID)
          apply (simp add: comp_assoc)
          apply (subst CCC_b, simp_all add: set_addvars set_diff)
          apply auto [1]
          apply (simp add: comp_assoc [THEN sym])
          apply (rule_tac v = v in par_switch_eq_dist_a, simp_all)
          apply (simp_all add: set_addvars set_diff)
          apply auto [3]
          apply (subst switch_comp_subst, simp_all)
          apply (auto simp add: set_addvars set_diff) [1]
          apply (auto simp add: set_addvars set_diff) [1]
          apply (subst append_assoc [THEN sym])
          apply (subst CCC_d, simp_all)
          apply (simp_all add: set_addvars set_diff)
          apply auto [3]
          apply (simp add: Subst_cancel_left_type)
          by (simp add: Subst_append)

         have "[In A \<oplus> (In B \<ominus> Out A) \<oplus> In C \<leadsto> (In A \<oplus> (In B \<ominus> Out A)) @ In C] oo
            ([In A \<oplus> (In B \<ominus> Out A) \<leadsto> In A @ (In B \<ominus> Out A)] oo Trs A \<parallel> [In B \<ominus> Out A \<leadsto> In B \<ominus> Out A] 
            oo [Out A @ (In B \<ominus> Out A) \<leadsto> (Out A \<ominus> In B) @ In B] oo [Out A \<ominus> In B \<leadsto> Out A \<ominus> In B] \<parallel> Trs B) \<parallel> Trs C 
            =
            [In A \<oplus> (In B \<ominus> Out A) \<oplus> In C \<leadsto> In A \<oplus> (In B \<oplus> In C \<ominus> Out A)] oo
            ([In A \<oplus> (In B \<oplus> In C \<ominus> Out A) \<leadsto> In A @ (In B \<oplus> In C \<ominus> Out A)] oo Trs A \<parallel> [In B \<oplus> In C \<ominus> Out A \<leadsto> In B \<oplus> In C \<ominus> Out A] 
            oo [Out A @ (In B \<oplus> In C \<ominus> Out A) \<leadsto> (Out A \<ominus> In B) @ (In B \<oplus> In C)] oo
             [Out A \<ominus> In B \<leadsto> Out A \<ominus> In B] \<parallel> ([In B \<oplus> In C \<leadsto> In B @ In C] oo Trs B \<parallel> Trs C))"
           apply (simp add: comp_parallel_distrib_a comp_parallel_distrib_b)
           apply (simp add: comp_assoc [THEN sym] par_assoc [THEN sym])
           by (simp add: A) 
          
          from this show "in_equiv ((A ;; B) ||| C) (CompA A (B ||| C))"
            apply (simp)
            by (simp add: in_equiv_def Comp_def Let_def Var_def diff_inter_left diff_inter_right  Parallel_def)
        qed
(*
      lemma in_equiv_CompA_Parallel_bb: "length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow>
        out A \<notin> set (Out C) \<Longrightarrow> out A \<notin> set (Out B)
        \<Longrightarrow> set (Out B) \<inter> set (Out C) = {}\<Longrightarrow> out A \<notin> set (In C) \<Longrightarrow> 
              in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        (*this can be done similar to in_equiv_CompA_Parallel_c*)
        apply (subgoal_tac "Out A = [out A]")
        apply (subgoal_tac " type_ok (A ;; B)")
        apply (subgoal_tac "out A \<in> set (In (C ||| B))", simp_all)
        apply (subgoal_tac "out A \<in> set (In (B ||| C))", simp_all)
        apply (subgoal_tac "Out (A ;; B) = Out B")
        apply (cut_tac A = "CompA A B" and B = "CompA A C" in in_equiv_switch_Parallel, simp_all)

        apply (rule_tac B = "(C ||| (A ;; B) ;; [[Out C @ Out B \<leadsto> Out B @ Out C]])" in in_equiv_tran, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply (rule type_ok_Comp, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply (rule_tac B = "((A ;; (C ||| B)) ;; [[Out C @ Out B \<leadsto> Out B @ Out C]])" in in_equiv_tran)
        apply (rule type_ok_Comp_a, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply auto [1]
        apply (simp add: VarSwitch_def)
        apply (subst type_ok_def, simp_all)
        apply auto [1]
        apply (simp add: VarSwitch_def)
        apply (auto simp add: set_diff set_addvars) [1]
        apply (rule type_ok_Comp_a, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply (rule in_equiv_Comp)
        apply (rule type_ok_Comp_a, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply auto [1]
        apply (simp add: VarSwitch_def)
        apply (subst type_ok_def, simp_all)
        apply auto [1]
        apply (cut_tac A = A and B = C and C = B in in_equiv_CompA_Parallel_c, simp_all)
        apply (rule in_equiv_eq)
        apply (subst type_ok_def, simp_all)
        apply (simp add: VarSwitch_def)
        apply auto [1]

        apply (subst Comp_assoc_new, simp_all)
        apply (rule type_ok_Parallel, simp_all)
                apply (simp add: VarSwitch_def)

        apply auto [1]
        apply (simp add: VarSwitch_def)
        apply (subst type_ok_def, simp_all)
        apply auto [1]
        apply (simp add: VarSwitch_def)
        apply (rule in_equiv_Comp, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply (simp add: in_equiv_eq)
        apply (rule in_equiv_sym)
        apply (rule type_ok_Comp_a, simp_all)
        apply (rule type_ok_Parallel, simp_all)
        apply (simp add: VarSwitch_def)
        apply auto [1]
        apply (simp add: VarSwitch_def)
        apply (subst type_ok_def, simp_all)

        apply (auto simp add: set_addvars set_diff) [2]
        apply (simp add: VarSwitch_def)
        apply (simp add: VarSwitch_def)
        apply (rule in_equiv_switch_Parallel, simp_all add:    VarSwitch_def)
        apply (simp add: Comp_def Let_def Var_def)
        apply (simp add: set_addvars)
        apply (simp add: set_addvars)
        apply (rule type_ok_Comp_a, simp_all)
        by (subst Out_out, simp_all)
*)
      lemma in_equiv_CompA_Parallel_d: "length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> out A \<notin> set (In C) \<Longrightarrow> 
              in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        by (simp add: in_equiv_def In_CompA set_addvars BBB_a Parallel_def )


      lemma in_equiv_CompA_Parallel: " deterministic (Trs A) \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> type_ok C \<Longrightarrow>
          (*set (Out B) \<inter> set (Out C) = {} \<Longrightarrow> (*from in_equiv_CompA_Parallel_b *)*)
          in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        apply (case_tac "out A \<in> set (In B)")
        apply (case_tac "out A \<in> set (In C)")
        apply (rule in_equiv_CompA_Parallel_a, simp)
        apply simp
        apply simp
        apply simp
        apply simp
        apply simp
        apply simp
        apply (rule in_equiv_CompA_Parallel_b, simp)
        apply simp
        apply simp
        apply simp
        apply simp
        apply simp
        apply simp
        apply (case_tac "out A \<in> set (In C)")
        apply (cut_tac in_equiv_CompA_Parallel_c, simp_all)
        by(cut_tac A = A and B = B and C = C in in_equiv_CompA_Parallel_d, simp_all)
 

      lemma fb_less_step_compA: "deterministic (Trs A) \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> type_ok A \<Longrightarrow> Type_OK As \<Longrightarrow> in_equiv (Parallel_list (fb_less_step A As)) (CompA A (Parallel_list As))"
        apply (induction As)
        apply (simp_all add: fb_less_step_def in_equiv_eq)
        apply (rule_tac B = "(CompA A a ||| CompA A (Parallel_list As))" in in_equiv_tran)
        apply (rule type_ok_CompA, simp_all)
        apply (rule type_ok_Parallel)
        apply (simp add: Type_OK_simp)
        apply (rule type_ok_parallel_list)
        apply (simp add: Type_OK_simp, safe)
        apply (simp add: Out_Parallel BBB_a Type_OK_out)
        apply (simp add: Type_OK_simp image_def)
        apply (rule in_equiv_Parallel)
        apply (rule type_ok_CompA, simp_all)
        apply (simp add: Type_OK_simp)
        apply (rule type_ok_CompA, simp_all)
        apply (rule type_ok_parallel_list, simp)
        apply (rule in_equiv_eq)
        apply (rule type_ok_CompA, simp_all)
        apply (simp add: Type_OK_simp)
        apply (rule in_equiv_CompA_Parallel, simp_all)
        apply (simp add: Type_OK_simp)
        by (rule type_ok_parallel_list, simp)
      
thm switch_par_comp_Subst
(*simp rules*)

      lemma switch_eq_Subst: "distinct x \<Longrightarrow> distinct u \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set v \<subseteq> set u \<Longrightarrow> TVs x = TVs u \<Longrightarrow> Subst x u y = v \<Longrightarrow> [x \<leadsto> y] = [u \<leadsto> v]"
        using Subst_switch_a by blast

      thm AAa

      lemma [simp]: "set y \<subseteq> set y1 \<Longrightarrow> distinct x1 \<Longrightarrow> TVs x1 = TVs y1 \<Longrightarrow> Subst x1 y1 (Subst y1 x1 y) = y"
        by (metis AAa length_TVs)
        

      lemma [simp]: "set z \<subseteq> set x \<Longrightarrow> TVs x  = TVs y \<Longrightarrow> set (Subst x y z) \<subseteq> set y"
        by (metis Subst_set_incl length_TVs)

      thm distinct_Subst

(******************)
      lemma distinct_Subst_aa: "\<And> y . 
            distinct y \<Longrightarrow> length x = length y \<Longrightarrow> a \<notin> set y \<Longrightarrow> set z \<inter> (set y - set x) = {} \<Longrightarrow> a \<noteq> aa \<Longrightarrow> a \<notin> set z \<Longrightarrow> aa \<notin> set z \<Longrightarrow> distinct z  \<Longrightarrow> aa \<in> set x \<Longrightarrow> subst x y a \<noteq> subst x y aa"
        apply (induction x, simp_all)
        apply (case_tac y, simp_all, safe)
        apply (metis subst_in_set subst_notin)
        apply (simp add: subst_in_set)
        apply (metis local.AA subst_notin) 
        by (metis local.AA subst_notin)

      lemma distinct_Subst_ba: "distinct y \<Longrightarrow> length x = length y \<Longrightarrow> set z \<inter> (set y - set x) = {} \<Longrightarrow> a \<notin> set z \<Longrightarrow> distinct z  \<Longrightarrow> a \<notin> set y \<Longrightarrow> subst x y a \<notin> set (Subst x y z)"
        apply (induction z, simp_all, safe)
        apply (simp add: distinct_Subst_a)
        by (simp add: distinct_Subst_aa)

      lemma distinct_Subst_ca: "distinct y \<Longrightarrow> length x = length y \<Longrightarrow> set z \<inter> (set y - set x) = {} \<Longrightarrow> a \<notin> set z \<Longrightarrow> distinct z \<Longrightarrow> a \<in> set x \<Longrightarrow> subst x y a \<notin> set (Subst x y z)"
        apply (induction z, simp_all, safe)
        apply (metis distinct_Subst_aa)
        by (metis local.AA)

      lemma [simp]: "set z \<inter> (set y - set x) = {} \<Longrightarrow>  distinct y \<Longrightarrow> distinct z \<Longrightarrow> length x = length y \<Longrightarrow> distinct (Subst x y z)"
        apply (induction z, simp_all, safe)
        apply (simp add: distinct_Subst_ba)
        by (simp add: distinct_Subst_ca)

(*end simp rules*)

      lemma deterministic_switch: "distinct x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> deterministic [x \<leadsto> y]"
        by (simp add: deterministic_def switch_dup)


      lemma deterministic_comp: "deterministic A \<Longrightarrow> deterministic B \<Longrightarrow> TO A = TI B \<Longrightarrow> deterministic (A oo B)"
        apply (simp add: deterministic_def)
        proof -
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
        apply (simp add: deterministic_def)            
        proof -
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
            apply (simp add: comp_assoc)
            by (simp add: comp_parallel_distrib)
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


      lemma deterministic_Comp: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> deterministic (Trs A) \<Longrightarrow> deterministic (Trs B) \<Longrightarrow> deterministic (Trs (A ;; B))"
        apply (simp add: Comp_def Let_def)
        apply (rule deterministic_comp)
        apply (rule deterministic_comp)
        apply (rule deterministic_comp)
        apply (rule deterministic_switch, simp_all)

        apply (rule deterministic_par, simp_all)
        apply (rule deterministic_switch, simp_all)
        apply (rule deterministic_switch, simp_all)

        apply (simp add: set_diff set_addvars Var_def set_inter)
        apply auto [1]
        apply (simp add: set_diff set_addvars Var_def set_inter)
        apply auto [1]

        apply (rule deterministic_par)
        apply (rule deterministic_switch)
        by simp_all

      lemma deterministic_CompA: "type_ok A \<Longrightarrow> type_ok B \<Longrightarrow> deterministic (Trs A) \<Longrightarrow> deterministic (Trs B) \<Longrightarrow> deterministic (Trs (CompA A B))"
        by (simp add: CompA_def deterministic_Comp)


      lemma parallel_list_empty[simp]: "parallel_list [] = ID []"
        by (simp add: parallel_list_def)

      lemma parallel_list_append: "parallel_list (As @ Bs) = parallel_list As \<parallel> parallel_list Bs"
        apply (induction As)
        apply (simp_all)
        by (simp add: parallel_list_cons par_assoc)

(*
      lemma par_swap_aux_a: "distinct p \<Longrightarrow> distinct (x @ y) \<Longrightarrow> distinct z \<Longrightarrow> [p \<leadsto> x @ y @ z] oo [x @ y \<leadsto> y @ x] \<parallel> [z \<leadsto> z] = [p \<leadsto> y @ x @ z]"
        proof -
          assume [simp]: "distinct p"
          assume [simp]: "distinct (x @ y)"
          assume [simp]: "distinct z"

          def w \<equiv> "x @ y"
          def z' \<equiv> "newvars w (TVs z)"

          have [simp]: "distinct x"
            using \<open>distinct (x @ y)\<close> distinct_append by blast

          have [simp]: "distinct y"
            using \<open>distinct (x @ y)\<close> distinct_append by blast

          have [simp]: "distinct z'"
            by (simp add: z'_def)

          have [simp]: "set x \<inter> set y = {}"
            using \<open>distinct (x @ y)\<close> by auto

          have Aa: "set (x @ y) \<inter> set z' = {}"
            by (simp only: z'_def w_def newvars_old_distinct_a)
            
          have [simp]: "set y \<inter> set z' = {}"
            apply (cut_tac Aa)
            by (simp add: set_addvars, auto)

          have [simp]: "set x \<inter> set z' = {}"
            apply (cut_tac Aa)
            by (simp add: set_addvars, auto)

          have [simp]: "length z' = length z"
            by (simp add: z'_def newvars_length TVs_def)

          have a: "Subst (x @ y @ z') (x @ y @ z) z' = z"
            by simp

          have b: "Subst (x @ y @ z') (x @ y @ z) (y @ x) = y @ x"
            apply (cut_tac x="x @ y" and x'="z'" and y="x@y" and y'=z and z="y@x" in Subst_not_in)
            apply simp_all
            by (simp add: Int_commute)

          have [simp]: "Subst (x @ y @ z') (x @ y @ z) (y @ x @ z') = (y @ x @ z)"
            apply (simp only: Subst_append a)
            apply (subgoal_tac "Subst (x @ y @ z') (x @ y @ z) y @ Subst (x @ y @ z') (x @ y @ z) x = Subst (x @ y @ z') (x @ y @ z) (y @ x)")
            apply (simp add: b)
            by (simp only: Subst_append[THEN sym]) 

          have "[p \<leadsto> x @ y @ z] oo [x @ y \<leadsto> y @ x] \<parallel> [z \<leadsto> z] = [p \<leadsto> x @ y @ z] oo [x @ y \<leadsto> y @ x] \<parallel> [z' \<leadsto> z']"
            by (simp add: z'_def switch_newvars)
          also have "... =  [p \<leadsto> x @ y @ z] oo [x @ y @ z'\<leadsto> y @ x @ z']"
            apply (subst par_switch)
            by (simp_all)
          also have "... = [p \<leadsto> y @ x @ z]"
            apply (subst switch_comp_subst, simp_all, auto)
            by (simp add: z'_def)
         finally show ?thesis
          by simp
       qed

*)
      thm switch_par

      lemma par_swap_aux: "distinct p \<Longrightarrow> distinct (v @ u @ w) \<Longrightarrow> 
          TI A = TVs x \<Longrightarrow> TI B = TVs y \<Longrightarrow> TI C = TVs z \<Longrightarrow>
          TO A = TVs u \<Longrightarrow> TO B = TVs v \<Longrightarrow> TO C = TVs w \<Longrightarrow>
          set x \<subseteq> set p \<Longrightarrow> set y \<subseteq> set p \<Longrightarrow> set z \<subseteq> set p \<Longrightarrow> set q \<subseteq> set (u @ v @ w) \<Longrightarrow>
          [p \<leadsto> x @ y @ z] oo (A \<parallel> B \<parallel> C) oo [u @ v @ w \<leadsto> q] = [p \<leadsto> y @ x @ z] oo (B \<parallel> A \<parallel> C) oo [v @ u @ w \<leadsto> q]"
        proof -
          def x' \<equiv> "newvars [] (TI A)"
          def y' \<equiv> "newvars x' (TI B)"
          def z' \<equiv> "newvars (x' @ y') (TI C)"
          assume " distinct (v @ u @ w)"
          from this have [simp]: "distinct u" and [simp]: "distinct v" and [simp]: "distinct w"
            and [simp]: "set u \<inter> set w = {}" and [simp]: "set v \<inter> set u = {}" and [simp]: "set v \<inter> set w = {}"
            by simp_all
          assume [simp]: "TI A = TVs x" and [simp]: "TI B = TVs y" and [simp]: "TI C = TVs z"
          assume [simp]: "TO A = TVs u" and [simp]: "TO B = TVs v" and [simp]: "TO C = TVs w"
          assume [simp]: "distinct p"
          assume [simp]: "set x \<subseteq> set p" and [simp]:"set y \<subseteq> set p" and [simp]: "set z \<subseteq> set p" and "set q \<subseteq> set (u @ v @ w)"

          have A: "distinct (x' @ y' @ z')"
            by (metis newvars_distinct newvars_old_distinct_a append_assoc distinct_append x'_def y'_def z'_def)

          have [simp]: "set x' \<inter> set y' = {}"
            by (simp add: y'_def)

          have [simp]: "length x' = length x"
            by (simp add: x'_def newvars_length )

          have [simp]: "length y' = length y"
            by (simp add: y'_def newvars_length )

          have [simp]: "length z' = length z"
            by (simp add: z'_def newvars_length )

          have [simp]: "set z' \<inter> set y' = {}"
            using A by auto

          have [simp]: "distinct y'"
            using A by auto

          have [simp]: "distinct x'"
            using A by auto

          have [simp]: "distinct z'"
            using A by auto

          have [simp]: "set x' \<inter> set z' = {}"
            using A by auto
            

          have [simp]: "Subst (x' @ y' @ z') (x @ y @ z) y' = y"
            by (simp )

          have [simp]: "Subst (x' @ y' @ z') (x @ y @ z) x' = x"
            apply (subst Subst_not_in)
            apply simp_all
            by (metis A Int_commute distinct_append set_append)

          have [simp]: "Subst (x' @ y' @ z') (x @ y @ z) z' = z"
            apply (simp )
            apply (subst Subst_not_in_a)
            apply simp_all
            using \<open>set z' \<inter> set y' = {}\<close> by blast
            

          have [simp]: "Subst (x' @ y' @ z') (x @ y @ z) (y' @ x' @ z') = y @ x @ z"
            by (simp add: Subst_append)

          have "[p \<leadsto> x @ y @ z] oo (A \<parallel> B \<parallel> C) oo [u @ v @ w \<leadsto> q] = [p \<leadsto> x @ y @ z] oo (([x' @ y' \<leadsto> y' @ x'] oo B \<parallel> A oo [v @ u \<leadsto> u @ v]) \<parallel> C) oo [u @ v @ w \<leadsto> q]"
            by (subst switch_par [THEN sym], simp_all add: x'_def y'_def)
          also have "... = [p \<leadsto> x @ y @ z] oo (([x' @ y' \<leadsto> y' @ x'] oo B \<parallel> A oo [v @ u \<leadsto> u @ v]) \<parallel> ([z' \<leadsto> z'] oo C oo [w \<leadsto> w])) oo [u @ v @ w \<leadsto> q]"
            by (simp add: z'_def)
          also have "... = [p \<leadsto> x @ y @ z] oo ([x' @ y' \<leadsto> y' @ x'] \<parallel> [z' \<leadsto> z'] oo B \<parallel> A \<parallel> C oo [v @ u \<leadsto> u @ v] \<parallel> [w \<leadsto> w]) oo [u @ v @ w \<leadsto> q]"
            by (simp add: comp_parallel_distrib x'_def y'_def z'_def)
          also have "... = [p \<leadsto> x @ y @ z] oo ([x' @ y' @ z' \<leadsto> y' @ x' @ z'] oo B \<parallel> A \<parallel> C oo [v @ u @ w \<leadsto> u @ v @ w]) oo [u @ v @ w \<leadsto> q]"
            apply (subst par_switch, simp_all)
            apply (metis newvars_old_distinct_a append_assoc distinct_append newvars_distinct x'_def y'_def z'_def)
            by (subst par_switch, simp_all)
          also have "... = ([p \<leadsto> x @ y @ z] oo [x' @ y' @ z' \<leadsto> y' @ x' @ z']) oo B \<parallel> A \<parallel> C oo ([v @ u @ w \<leadsto> u @ v @ w] oo [u @ v @ w \<leadsto> q])"
            by (simp add: comp_assoc y'_def x'_def z'_def )
          also have "... = ([p \<leadsto> x @ y @ z] oo [x' @ y' @ z' \<leadsto> y' @ x' @ z']) oo B \<parallel> A \<parallel> C oo [v @ u @ w \<leadsto> q]"
            apply (subst switch_comp, simp_all add:)
            using perm_tp perm_union_left apply fastforce
            using \<open>set q \<subseteq> set (u @ v @ w)\<close> by auto
            
(*
            by (metis \<open>distinct (v @ u @ w)\<close> append_assoc perm_tp perm_union_left switch_comp)
*)
          also have "... =  [p \<leadsto> y @ x @ z] oo B \<parallel> A \<parallel> C oo [v @ u @ w \<leadsto> q]"
            apply (cut_tac A, subst switch_comp_subst, simp_all)
            apply auto [1]
            by (simp add: x'_def y'_def z'_def)

          finally show "[p \<leadsto> x @ y @ z] oo (A \<parallel> B \<parallel> C) oo [u @ v @ w \<leadsto> q] = [p \<leadsto> y @ x @ z] oo (B \<parallel> A \<parallel> C) oo [v @ u @ w \<leadsto> q]"
            by simp
        qed
(*
      lemma par_swap_aux_b: "distinct p \<Longrightarrow> distinct (v @ u) \<Longrightarrow> 
          TI A = TVs x \<Longrightarrow> TI B = TVs y \<Longrightarrow>
          TO A = TVs u \<Longrightarrow> TO B = TVs v \<Longrightarrow>      
          [p \<leadsto> x @ y] oo (A \<parallel> B) oo [u @ v \<leadsto> q] = [p \<leadsto> y @ x] oo (B \<parallel> A) oo [v @ u \<leadsto> q]"
        proof -
          assume [simp]: "distinct p"
          assume [simp]: "distinct (v @ u)"
          assume [simp]: "TI A = TVs x"
          assume [simp]: "TI B = TVs y"
          assume [simp]: "TO A = TVs u"
          assume [simp]: "TO B = TVs v"

          def x' \<equiv> "newvars [] (TI A)"
          def y' \<equiv> "newvars x' (TI B)"

          have [simp]: "distinct x'"
            by (simp add: x'_def)          

          have [simp]: "distinct y'"
            by (simp add: y'_def)          

          have [simp]: "set x' \<inter> set y' = {}"
            by (simp add: y'_def)

          have [simp]: "distinct v"
            using \<open>distinct (v @ u)\<close> distinct_append by blast

          have [simp]: "distinct u"
            using \<open>distinct (v @ u)\<close> distinct_append by blast

          have [simp]: "set v \<inter> set u = {}"
            using \<open>distinct (v @ u)\<close> by auto

          have [simp]: "TVs x = TVs x'"
            by (simp add: x'_def)

          have [simp]: "TVs y = TVs y'"
            by (simp add: y'_def)

          have [simp]: "length x' = length x"
            by (simp add: x'_def newvars_length TVs_def)

          have [simp]: "length y' = length y"
            by (simp add: y'_def newvars_length TVs_def)

          have [simp]: "Subst (x' @ y') (x @ y) y' = y"
            by simp

          have [simp]: "Subst (x' @ y') (x @ y) x' = x"
            by (simp add:  Int_commute)

          have [simp]: "Subst (x' @ y') (x @ y) (y' @ x') = y @ x"
            by (simp add: Subst_append)

          have "[p \<leadsto> x @ y] oo (A \<parallel> B) oo [u @ v \<leadsto> q] = [p \<leadsto> x @ y] oo ([x' @ y' \<leadsto> y' @ x'] oo B \<parallel> A oo [v @ u \<leadsto> u @ v]) oo [u @ v \<leadsto> q]"
            by (subst switch_par, simp_all)
          also have "... = ([p \<leadsto> x @ y] oo [x' @ y' \<leadsto> y' @ x']) oo B \<parallel> A oo ([v @ u \<leadsto> u @ v] oo [u @ v \<leadsto> q])"
            by (simp add: comp_assoc_middle_ext )
          also have "... = [p \<leadsto> Subst (x' @ y') (x @ y) (y' @ x')] oo B \<parallel> A oo ([v @ u \<leadsto> u @ v] oo [u @ v \<leadsto> q])"
            by (simp add: switch_comp_subst)
          also have "... = [p \<leadsto> y @ x] oo B \<parallel> A oo ([v @ u \<leadsto> u @ v] oo [u @ v \<leadsto> q])"
            by simp
          also have "... = [p \<leadsto> y @ x] oo B \<parallel> A oo [v @ u \<leadsto> q]"
            by (simp add: switch_comp perm_tp)

          finally show ?thesis
            by simp
        qed
*)
      lemma Type_OK_distinct: "Type_OK As \<Longrightarrow> distinct As"
        by (induction As, simp_all add: Type_OK_simp, auto)

      lemma TI_parallel_list_a: "TI (parallel_list As) = concat (map TI As)"
        by (induction As, simp_all add: parallel_list_cons)


      lemma fb_CompA_aux: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A = a \<Longrightarrow> a \<notin> set (In A) \<Longrightarrow>
        InAs = In (Parallel_list As) \<Longrightarrow> OutAs = Out (Parallel_list As) \<Longrightarrow> perm (a # y) InAs \<Longrightarrow> perm (a # z) OutAs \<Longrightarrow>
        InAs' = In (Parallel_list (As \<ominus> [A])) \<Longrightarrow>
        fb ([a # y \<leadsto>  concat (map In As)] oo parallel_list (map Trs As) oo [OutAs \<leadsto> a # z]) =
                [y \<leadsto> In A @ (InAs' \<ominus> [a])] 
                oo (Trs A \<parallel> [(InAs' \<ominus> [a]) \<leadsto>  (InAs' \<ominus> [a])])
                oo [a # (InAs' \<ominus> [a]) \<leadsto> InAs'] oo Trs (Parallel_list (As \<ominus> [A])) 
                oo [OutAs \<ominus> [a] \<leadsto> z]" (is "_\<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _  \<Longrightarrow> _ \<Longrightarrow> _  \<Longrightarrow> fb ?Ta = ?Tb")
        proof -
          assume [simp]:"Type_OK As"
          assume [simp]:"A \<in> set As"
          assume X[simp]: "out A = a"
          assume InAs': "InAs' = In (Parallel_list (As \<ominus> [A]))"

          assume InAs: "InAs = In (Parallel_list As)"
          assume OutAs: "OutAs = Out (Parallel_list As)"

          assume permInAs: "perm (a # y) InAs"
          assume PermOutAs: "perm (a # z) OutAs"

          assume [simp]: "a \<notin> set (In A)"
          
          obtain Cs Ds where A: "As = Cs @ (A # Ds)" by (cut_tac split_list, auto)

          from OutAs have OutAs_simp: "OutAs = concat (map Out As)"
            by (simp add: OutAs Out_Parallel)

          have [simp]: "distinct InAs"
            using InAs \<open>Type_OK As\<close> type_ok_def type_ok_parallel_list by blast

          have "distinct OutAs"
            using Type_OK_def OutAs_simp \<open>Type_OK As\<close> by blast

          have distinctAs: "distinct As"
            by (rule Type_OK_distinct, simp)

          from distinctAs have Ba: "As \<ominus> [A] = Cs @ Ds"
            apply (simp add: A union_diff)
            by (simp add: AAA_c)

          have [simp]: "Type_OK (Cs @ Ds)"
            apply (subgoal_tac "Type_OK As")
            apply (unfold Type_OK_simp A) [1]
            by (simp_all)


          have [simp]: "distinct InAs'"
            apply (simp add: InAs' Ba)
            using \<open>Type_OK (Cs @ Ds)\<close> type_ok_def type_ok_parallel_list by blast


          def C \<equiv> "parallel_list (map Trs Cs)"
          def D \<equiv> "parallel_list (map Trs Ds)"
          def InCs \<equiv> "concat (map In Cs)"
          def InDs \<equiv> "concat (map In Ds)"
          def OutCs \<equiv> "Out (Parallel_list Cs)"
          def OutDs \<equiv> "Out (Parallel_list Ds)"

          have [simp]: "Out A = [a]"
            using Type_OK_out \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> by blast
        
          from A have [simp]: "parallel_list (map Trs As) = C \<parallel> Trs A \<parallel> D"
            by (simp add: parallel_list_append parallel_list_cons C_def D_def par_assoc)


          from A have [simp]: "concat (map In As) = InCs @ In A @ InDs"
            by (simp add:  InCs_def InDs_def par_assoc) 

          from A have [simp]: "OutAs = OutCs @ [a] @ OutDs"
            by (simp add:  OutCs_def OutDs_def par_assoc OutAs Out_Parallel)

          have [simp]:"a \<notin> set y" and [simp]: "distinct y"
            apply (meson \<open>distinct InAs\<close> dist_perm distinct.simps(2) permInAs perm_sym)
            by (meson \<open>distinct InAs\<close> dist_perm distinct.simps(2) permInAs perm_sym)
    
          have [simp]: "distinct OutCs"
            by (metis Type_OK_def OutAs_simp \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> distinct_append)

          have [simp]: " a \<notin> set OutDs"
            by (metis OutAs_simp Out_Parallel \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> append.simps(2) disjoint_iff_not_equal distinct_append list.set_intros(1) type_ok_def type_ok_parallel_list)
  
          have [simp]: " distinct OutDs "
            by (metis Type_OK_def OutAs_simp \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> distinct_append)

          have [simp]: " a \<notin> set OutCs "
            by (metis OutAs_simp Out_Parallel \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> append.simps(2) disjoint_iff_not_equal distinct_append list.set_intros(1) type_ok_def type_ok_parallel_list)

          have [simp]: "set OutCs \<inter> set OutDs = {}"
            by (metis Type_OK_def OutAs_simp \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> append_assoc dist_perm distinct_append perm_tp)
(*
          have [simp]: "TI (Trs A) = TVs (In A)"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "A \<in> set As")
            apply (simp add: Type_OK_def type_ok_def)
            by simp_all
*)
          have Type_OK_Cs: "Type_OK Cs"
            apply (subgoal_tac "Type_OK As")
            apply (unfold A Type_OK_simp) [1]
            by simp_all

          from this have [simp]: " TI C = TVs InCs"
            apply (simp add: C_def InCs_def)
            apply (subst TI_parallel_list)
            by (simp add: Type_OK_def, simp)

          have Type_OK_Ds: "Type_OK Ds"
            apply (subgoal_tac "Type_OK As")
            apply (unfold A Type_OK_simp) [1]
            by simp_all

          from this have [simp]: " TI D = TVs InDs"
            apply (simp add: D_def InDs_def)
            apply (subst TI_parallel_list)
            by (simp add: Type_OK_def, simp)


          from Type_OK_Cs have [simp]: " TO C = TVs OutCs"
            apply (simp add: C_def OutCs_def)
            apply (subst TO_parallel_list)
            apply (simp add: Type_OK_def)
            by (simp add: Out_Parallel)

          from Type_OK_Ds have [simp]: "TO D = TVs OutDs"
            apply (simp add: D_def OutDs_def)
            apply (subst TO_parallel_list)
            apply (simp add: Type_OK_def)
            by (simp add: Out_Parallel)

          from \<open>Type_OK As\<close> have [simp]: "type_ok A"
            by (unfold Type_OK_def, simp)
            
thm perm_set_eq

          have B: "?Ta = [a # y \<leadsto> In A @ InCs @ InDs] oo (Trs A \<parallel> C \<parallel> D) oo [ [ a ] @ OutCs @ OutDs \<leadsto> a # z]"
            apply (subst par_swap_aux, simp_all)
            apply (cut_tac \<open>perm (a#y) InAs\<close>)
            apply (drule perm_set_eq, simp add: InAs In_Parallel)
            apply auto [1]
            apply (cut_tac \<open>perm (a#y) InAs\<close>)
            apply (drule perm_set_eq, simp add: InAs InCs_def A In_Parallel)
            apply auto [1]
            apply (cut_tac \<open>perm (a#y) InAs\<close>)
            apply (drule perm_set_eq, simp add: InAs InDs_def A In_Parallel)
            apply auto [1]
            apply (cut_tac \<open>perm (a # z) OutAs\<close>)
            by (drule perm_set_eq, simp add: OutCs_def OutDs_def A Out_Parallel In_Parallel, auto)

            

          def E \<equiv> "C \<parallel> D"
          def InE \<equiv> "InCs @ InDs"
          def OutE \<equiv> "OutCs @ OutDs"

          from B have C: "?Ta = [a # y \<leadsto> In A @ InE] oo (Trs A \<parallel> E) oo [ [a ] @ OutE \<leadsto> a # z]"
            by (unfold E_def InE_def OutE_def par_assoc, simp)

          def y' \<equiv> "newvars (a#y) (TVs y)"

          have [simp]: "a \<notin> set y'"
            by (metis newvars_old_distinct_a IntI distinct.simps(2) distinct_singleton list.set(1) list.set_intros(1) y'_def)

          have [simp]: "distinct y'"
            by (simp add: y'_def)

          have [simp]: "set y \<inter> set y' = {}"
            by (metis Int_insert_right_if0 \<open>a \<notin> set y'\<close> inf.commute list.set(2) newvars_old_distinct y'_def)

          have [simp]: "TVs y' = TVs y"
            by (simp add: y'_def)

          have [simp]: "length y' = length y"
            apply (simp add: y'_def)
            by (simp add: newvars_length)

          have [simp]: "Subst (y @ y') (y @ y) y = y"
            by (simp add: inf_aci(1))

          have [simp]: "Subst (y @ y') (y @ y) y' = y"
            using Subst_cons_aux_a \<open>TVs y' = TVs y\<close> \<open>distinct y'\<close> \<open>distinct y\<close> \<open>set y \<inter> set y' = {}\<close> type_length by blast

          have [simp]: "Subst (a # y @ y') (a # y @ y) (y @ a # y') = y @ a # y"
            by (simp add: Subst_append)

          have Au: "set InAs = set InCs \<union> (set (In A) \<union> set InDs)"
            by (simp add: InAs In_Parallel A InCs_def InDs_def, auto)

          have Av: "set InAs = insert a (set y)"
            using permInAs perm_set_eq by force

          have [simp]: "set (In A) \<subseteq> set y"
            by (metis Au Av Un_left_commute Un_upper1 \<open>a \<notin> set (In A)\<close> subset_insert)
            

          have [simp]: "set (In A) \<inter> set y' = {}"
            using \<open>set (In A) \<subseteq> set y\<close> \<open>set y \<inter> set y' = {}\<close> by blast

          have [simp]: "Subst (y @ a # y') (y @ a # y) (In A) = In A"
            by (simp add: Subst_cancel_right)

          have [simp]: "set InCs \<subseteq> insert a (set y)"
            using Au Av by auto

          have [simp]: "Subst (a # y') (a # y) (Subst (a # y) (a # y') InCs) = InCs"
            by (subst Subst_Subst_id, simp_all) 

          from this have [simp]: "Subst y' y (Subst y y' InCs) = InCs"
            by (simp add: Subst_cancel_right_a)

          have [simp]: "set InDs \<subseteq> insert a (set y)"
            using Au Av by auto

          from this have [simp]: "Subst (a # y') (a # y) (Subst (a # y) (a # y') InDs) = InDs"
            by (subst Subst_Subst_id, simp_all)

          from this have [simp]: "Subst y' y (Subst y y' InDs) = InDs"
            by (simp add: Subst_cancel_right_a)

          have [simp]: "Subst (y @ a # y') (y @ a # y) (In A @ Subst (a # y) (a # y') InE) = In A @ InE"
            by (simp add: InE_def Subst_append Subst_cancel_right)
            
          have [simp]: "a \<notin> set OutE"
            by (simp add: OutE_def)

          have [simp]: "distinct OutE"
            by (simp add: OutE_def)

          thm perm_set
          have [simp]: "set z \<subseteq> set OutE"
              proof -
                have "insert a (set z) = insert a (set OutE)"
                  using OutE_def PermOutAs perm_set_eq by fastforce
                then show ?thesis
                  by (metis (no_types) Diff_insert_absorb PermOutAs \<open>a \<notin> set OutE\<close> \<open>distinct OutAs\<close> dist_perm distinct.simps(2) equalityE perm_sym)
              qed

          have [simp]: " TI E = TVs (Subst (a # y) (a # y') InE)"
            by (simp add: InE_def E_def Subst_append)

          have [simp]: "TO E = TVs OutE"
            by (simp add: OutE_def E_def)


          def w \<equiv> "InAs' \<ominus> [a]"
          have [simp]: "a \<notin> set w"
            by (simp add: w_def set_diff)
          have [simp]:"distinct w"
            by (simp add: w_def )

          have [simp]:"TVs (Subst y y' w) = TVs w"
            by simp

          have [simp]: "TVs (Subst (a # w) (a # Subst y y' w) InAs') = TVs InAs'"
            by simp

          have [simp]: "set w \<subseteq> set y"
            using Av by (simp add: w_def set_diff InAs' In_Parallel InAs, auto)

          have [simp]: "set InAs' \<subseteq> insert a (set w)"
            using Av by (simp add: w_def set_diff InAs' In_Parallel InAs, auto)

          have [simp]: "set InE \<subseteq> set InAs'"
            using \<open>distinct As\<close>
            by (simp add: InE_def InAs' In_Parallel InCs_def InDs_def A set_diff)

          have [simp]: "set (Subst (a # y) (a # y') InE) \<subseteq> insert a (set y')"
            apply (cut_tac x = "a # y" and y = "a # y'" and z = InE in Subst_set_incl)
            apply simp_all
            apply (rule_tac y = " set InAs'" in order_trans, simp_all)
            apply (rule_tac y = "insert a (set w)"  in order_trans, simp_all)
            by (rule_tac y = "(set y)"  in order_trans, auto)

          have [simp]: "Subst InAs' (Subst (a # w) (a # Subst y y' w) InAs') InE = Subst (a # y) (a # y') InE"
            proof -
              have "Subst InAs' (Subst (a # w) (a # Subst y y' w) InAs') InE = Subst InAs' (Subst (a # w) (Subst y y' (a # w)) InAs') InE"
                by simp
              also have "... = Subst InAs' (Subst y y' InAs') InE"
                by (subst Subst_Subst, simp_all)
              also have "... =  Subst y y' InE"
                by (subst Subst_Subst, simp_all)
              also have "... = Subst (a # y) (a # y') InE"
                by (simp add: Subst_cancel_right_a)
              finally show ?thesis by simp
            qed

          have [simp]: "TVs (Subst (a # y) (a # y') InE) = TVs InE"
            using E_def InE_def \<open>TI E = TVs (Subst (a # y) (a # y') InE)\<close> by auto


          have [simp]: "set (Subst y y' w) \<subseteq> set y'"
            by (simp add: Subst_set_incl)

          have [simp]: "Subst (y @ y') (y @ y) (In A @ Subst y y' w) = In A @ w"
            by (simp add: Subst_append Subst_cancel_right)
          
          have Aa: "OutCs @ a # OutDs \<ominus> [a] = OutE"
            by (simp add: AAA_c OutE_def union_diff)


          from Ba have Ab: "[InAs' \<leadsto> InE] oo E = Trs (Parallel_list (As \<ominus> [A]))"
            by (simp add: E_def Trs_Parallel_list parallel_list_append C_def D_def InE_def InCs_def InDs_def InAs')

          have bb: "Subst y' y (Subst y y' InE) = InE"
            by (simp add: InE_def Subst_append)

   thm set_SubstI


          have D: "[a # y' \<leadsto> Subst (a # y) (a # y') InE] = [a # y' \<leadsto> a # (Subst y y' w)] oo [a # w \<leadsto> InAs'] oo [InAs' \<leadsto> InE]" (is "_ = ?Tx")
            apply (subst switch_comp_subst, simp_all)
            apply (simp add: subset_insertI2)
            apply (subst switch_comp_subst, simp_all)
            apply (cut_tac \<open> perm (a # y) InAs\<close>)
            apply (drule perm_set_eq)
            apply (simp add:  w_def )
            apply (rule set_SubstI, simp_all)
            apply (subgoal_tac "set (Subst y y' (InAs' \<ominus> [a])) \<subseteq> insert a (set y')", simp)
            apply (auto simp add: InAs' set_diff) [1]
            apply (rule set_SubstI, simp_all)
            by (simp add: InAs InAs' set_diff In_Parallel, auto)

          have aa: "Subst y' y (In A) = In A"
            proof -
              have f1: "set y \<inter> set y' = {}"
                by (metis (no_types) insert_disjoint(1) list.set(2) newvars_old_distinct_a y'_def)
              have "set y \<inter> set (In A) = set (In A)"
                using \<open>set (In A) \<subseteq> set y\<close> by blast
              then have "set y' \<inter> set (In A) = {}"
                using f1 by blast
              then show ?thesis
                by (simp add: TVs_def newvars_length)
            qed


          have cc: "Subst y' y (In A @ Subst y y' InE) = In A @ InE"
            by (simp add: Subst_append aa bb)

          have [simp]: "set (In A) \<subseteq> insert a (set y \<union> set y')"
            apply (cut_tac \<open> perm (a # y) InAs\<close>)
            apply (drule perm_set_eq)
            by (simp add: InAs In_Parallel, auto)

          have [simp]: "set InE - insert a (set y) \<subseteq> insert a (set y \<union> set y')"
            apply (cut_tac \<open> perm (a # y) InAs\<close>)
            apply (drule perm_set_eq)
            by (simp add: InE_def InAs A InCs_def InDs_def In_Parallel, auto)

          have [simp]: "set (Subst (a # y) (a # y') InE) \<subseteq> insert a (set y \<union> set y')"
            by (rule set_SubstI, simp_all, auto)

          have [simp]: "set (In A) \<subseteq> set y \<union> set y'"
            apply (cut_tac \<open> perm (a # y) InAs\<close>)
            apply (drule perm_set_eq)
            apply (simp add: InAs In_Parallel)
            apply (subst (asm) set_eq_iff, auto)
            by (drule_tac x = x in spec, auto)

          have [simp]: "set (Subst y y' w) \<subseteq> set y \<union> set y'"
            apply (rule set_SubstI, simp_all)
            apply (simp add: w_def)
            apply (cut_tac \<open> perm (a # y) InAs\<close>)
            apply (drule perm_set_eq)
            by (simp add: set_diff InAs InAs' In_Parallel, auto)


          have "[a # y \<leadsto> In A @ InE] = [a # y \<leadsto> a # y @ y] oo [a # y @ y' \<leadsto> y @ a # y'] oo [y @ a # y' \<leadsto> In A @ (Subst (a # y) (a # y') InE)]" (is "?Tc = ?Td")
            by (simp add: switch_comp_subst cc)
            

          from this have "fb ?Ta = fb (?Td oo (Trs A \<parallel> E) oo [ [a] @ OutE \<leadsto> a # z])"
            by (subst C, simp)
          also have "... =  fb ([ [a]\<leadsto> [a] ] \<parallel> [y \<leadsto> y @ y] oo [a # y @ y' \<leadsto> y @ a # y'] oo [y @ a # y' \<leadsto> In A @ Subst (a # y) (a # y') InE] oo Trs A \<parallel> E oo [ [a] \<leadsto> [a] ] \<parallel> [OutE \<leadsto> z])"
            by (simp add: par_switch)
          also have "... = fb  ([ [a]\<leadsto> [a] ] \<parallel> [y \<leadsto> y @ y] oo ([a # y @ y' \<leadsto> y @ a # y'] oo ([y @ a # y' \<leadsto> In A @ Subst (a # y) (a # y') InE] oo Trs A \<parallel> E)) oo [ [a] \<leadsto> [a] ] \<parallel> [OutE \<leadsto> z])"
            by (simp add: comp_assoc )
          also have "... =  [y \<leadsto> y @ y] oo fb  ( ([a # y @ y' \<leadsto> y @ a # y'] oo ([y @ a # y' \<leadsto> In A @ Subst (a # y) (a # y') InE] oo Trs A \<parallel> E))) oo [OutE \<leadsto> z]"
            apply (subgoal_tac "[ [a] \<leadsto> [a] ] = ID ([TV a])", simp)
            apply (subst fb_comp_fbtype, simp_all)
            apply (simp add: fbtype_def )
            by (simp add: distinct_id)
          also have "... =  [y \<leadsto> y @ y] oo fb  ( ([a # y @ y' \<leadsto> y @ a # y'] oo ([y \<leadsto> In A] \<parallel> [a # y' \<leadsto> Subst (a # y) (a # y') InE] oo Trs A \<parallel> E))) oo [OutE \<leadsto> z]"
            by (subst par_switch, simp_all)
          also have "... = [y \<leadsto> y @ y] oo (fb ^^ (length [a]))  ([ [a] @ y @ y' \<leadsto> y @ [a] @ y'] oo ([y \<leadsto> In A] oo Trs A ) \<parallel> ([ [a] @ y' \<leadsto> Subst (a # y) (a # y') InE] oo E)) oo [OutE \<leadsto> z]"
            by (simp add: comp_parallel_distrib)
          also have "... = [y \<leadsto> y @ y] oo (([y \<leadsto> In A] oo Trs A) \<parallel> ID (TVs y) oo ([a # y' \<leadsto> Subst (a # y) (a # y') InE] oo E)) oo [OutE \<leadsto> z]"
            apply (subst fb_par_serial [of _ _ _ "[]"])
            by (simp_all)
          also have "... = [y \<leadsto> y @ y] oo (([y \<leadsto> In A] oo Trs A) \<parallel> [y \<leadsto> y] oo ([a # y' \<leadsto> Subst (a # y) (a # y') InE] oo E)) oo [OutE \<leadsto> z]"
            by (simp add: distinct_id)
          also have "... = [y \<leadsto> y @ y] oo ([y \<leadsto> In A] oo Trs A) \<parallel> [y \<leadsto> y] oo [a # y' \<leadsto> Subst (a # y) (a # y') InE] oo E oo [OutE \<leadsto> z]"
            by (simp add: comp_assoc )
          also have "... = [y \<leadsto> y @ y] oo ([y \<leadsto> In A] oo Trs A) \<parallel> [y \<leadsto> y] oo ?Tx oo E oo [OutE \<leadsto> z]"
            by (simp add: D)
          also have "... = [y \<leadsto> y @ y] oo (([y \<leadsto> In A] oo Trs A) \<parallel> [y \<leadsto> y] oo [a # y' \<leadsto> a # Subst y y' w]) oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: comp_assoc)
          also have "... = [y \<leadsto> y @ y] oo (([y \<leadsto> In A] oo Trs A) \<parallel> [y' \<leadsto> y'] oo [a # y' \<leadsto> a # Subst y y' w]) oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: distinct_id)
          also have "... = [y \<leadsto> y @ y] oo (([y \<leadsto> In A] oo Trs A) \<parallel> [y' \<leadsto> y'] oo [ [a] \<leadsto> [a] ] \<parallel> [y' \<leadsto> Subst y y' w]) oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: par_switch)
          also have "... = [y \<leadsto> y @ y] oo (([y \<leadsto> In A] oo Trs A) \<parallel> [y' \<leadsto> Subst y y' w]) oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: comp_parallel_distrib)
          also have "... = [y \<leadsto> y @ y] oo ([y \<leadsto> In A] \<parallel> [y' \<leadsto> Subst y y' w] oo Trs A \<parallel> [w \<leadsto>w]) oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: comp_parallel_distrib)

          also have "... = [y \<leadsto> y @ y] oo ([y @ y' \<leadsto> In A @ Subst y y' w] oo Trs A \<parallel> [w \<leadsto>w]) oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: par_switch)

          also have "... = [y \<leadsto> y @ y] oo [y @ y' \<leadsto> In A @ Subst y y' w] oo Trs A \<parallel> [w \<leadsto>w] oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (simp add: comp_assoc)

          also have "... = [y \<leadsto> In A @ w] oo Trs A \<parallel> [w \<leadsto>w] oo [a # w \<leadsto> InAs'] oo ([InAs' \<leadsto> InE] oo E) oo [OutE \<leadsto> z]"
            by (subst switch_comp_subst, simp_all)
            
            
          also have "... = ?Tb"
            by (simp add: w_def Aa Ab)

          finally show "fb ?Ta = ?Tb"
            by simp
        qed

      lemma [simp]: "perm (a # x) (a # y) = perm x y"
        by (simp add: perm_def)

      lemma fb_CompA: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A = a \<Longrightarrow> a \<notin> set (In A) \<Longrightarrow> C = CompA A  (Parallel_list (As \<ominus> [A])) \<Longrightarrow>
         OutAs = Out (Parallel_list As) \<Longrightarrow> perm y (In C) \<Longrightarrow> perm z (Out C) \<Longrightarrow> B \<in> set As - {A} \<Longrightarrow> a \<in> set (In B) \<Longrightarrow>
         fb ([a # y \<leadsto> concat (map In As)] oo parallel_list (map Trs As) oo [OutAs \<leadsto> a # z]) = [y \<leadsto> In C] oo Trs C oo [Out C \<leadsto> z]"

         proof -
          assume [simp]: "Type_OK As"
          assume [simp]: "a \<notin> set (In A)"
          assume [simp]: "A \<in> set As"
          assume [simp]: "out A = a"
          assume [simp]: "OutAs = Out (Parallel_list As)"
          assume C: "C = CompA A  (Parallel_list (As \<ominus> [A]))"
          assume Au: "perm y (In C)"
          assume Av: "perm z (Out C)"
          assume "B \<in> set As - {A}" and "a \<in> set (In B)"

          from this have [simp]: "\<exists>x\<in>set As - {A}. a \<in> set (In x)"
            by blast

          from this have A[simp]: "a \<in> set (In (Parallel_list (As \<ominus> [A])))"
            by (subst In_Parallel, simp add: set_diff)

          thm perm_trans
          have [simp]: "length (Out A) = Suc 0"
            using \<open>Type_OK As\<close> \<open>A \<in> set As\<close> by (simp add: Type_OK_def)

          have [simp]: "Var A (Parallel_list (As \<ominus> [A])) = [a]"
            by (simp add: Var_def In_Parallel Out_out set_diff)



          def InAs' \<equiv> "In (Parallel_list (As \<ominus> [A]))"

          have Ax: "type_ok A"
            using \<open>Type_OK As\<close> \<open>A \<in> set As\<close> by (unfold Type_OK_def, simp)
            
          from Ax have [simp]: "TI (Trs A) = TVs (In A)"
            by simp

          from Ax have [simp]: "TO (Trs A) = [TV a]"
            by (simp add:  Out_out)

          have "Type_OK (As \<ominus> [A])"
            using \<open>Type_OK As\<close> by (unfold Type_OK_simp, simp add: set_diff BBB_c)

          from this have Ay: "type_ok (Parallel_list (As \<ominus> [A]))"
            using type_ok_parallel_list by blast
            

          from this have [simp]: "TI (Trs (Parallel_list (As \<ominus> [A]))) = TVs InAs'"
            by (simp add:  In_Parallel Trs_Parallel_list InAs'_def)

          obtain Cs Ds where A: "As = Cs @ (A # Ds)" by (cut_tac split_list, auto)

          have distinctAs: "distinct As"
            by (rule Type_OK_distinct, simp)

          from distinctAs have [simp]: "Cs \<ominus> [A] = Cs"
            apply (simp add: A, safe)
            by (simp add: AAA_c)

          from distinctAs have [simp]: "Ds \<ominus> [A] = Ds"
            apply (simp add: A, safe)
            by (simp add: AAA_c)

          from distinctAs and \<open>Type_OK As\<close> have [simp]: "\<forall>aa\<in>set Cs. a \<notin> set (Out aa)"
            by (simp add: A Type_OK_simp Out_out, auto)

         from distinctAs and \<open>Type_OK As\<close> have [simp]: "\<forall>aa\<in>set Ds. a \<notin> set (Out aa)"
            by (simp add: A Type_OK_simp Out_out, auto)

          have [simp]: "Out (Parallel_list (As \<ominus> [A])) = (Out (Parallel_list As) \<ominus> [a])"
            by (simp add: Out_Parallel A Out_out union_diff AAA_c)

          have type_ok_C: "type_ok C"
            apply (simp add: C)
            apply (subst type_ok_Comp, simp_all)
            using Ax Ay apply simp_all
            by (simp add: Out_out Out_Parallel set_diff)

          have [simp]: "perm (a # z) (Out (Parallel_list As))"
            using Av apply (rule_tac y = "a # Out C" in perm_trans, simp_all)
            apply (subst set_perm, simp_all, safe)
            apply (simp add: C Comp_def Let_def Out_Parallel set_diff)
            using \<open>Type_OK As\<close> apply (simp add: A Type_OK_simp Out_out)
            apply auto [1]
            using \<open>type_ok C\<close> type_ok_def apply blast
            using Type_OK_def BaseOperation_axioms Out_Parallel apply fastforce
            apply (simp_all add: Out_Parallel A Out_out union_diff AAA_c)
            apply (simp_all add: C Comp_def Let_def Out_Parallel set_diff Out_out)
            apply auto [1]
            apply (simp_all add: A)
            apply auto
            apply (metis Un_Diff Un_insert_left \<open>(Cs \<ominus> [A]) = Cs\<close> \<open>(Ds \<ominus> [A]) = Ds\<close> insert_Diff insert_iff list.set(1) list.simps(15) set_diff)
            by (metis Un_Diff Un_iff \<open>(Ds \<ominus> [A]) = Ds\<close> empty_set list.simps(15) set_diff)
            

          from type_ok_C have dist_C: "distinct (In C)"
            by (simp)
            
          from dist_C and Au have [simp]: "distinct y"
            using dist_perm perm_sym by blast

          have [simp]: "perm y (In A \<oplus> (InAs' \<ominus> [a]))"
            using Au by (simp add: InAs'_def C Comp_def Let_def)

          have Ay: "type_ok (Parallel_list As)"
            using \<open>Type_OK As\<close> type_ok_parallel_list by blast

          have [simp]: "perm (a # y) (In (Parallel_list As))"
            using Au apply (rule_tac y = "a # In C" in perm_trans, simp_all)
            apply (subst set_perm)
            using dist_C apply simp_all
            apply (simp add: C In_CompA Out_out Comp_def Let_def  set_diff set_addvars)
            using Ay apply (simp)
            using \<open>B \<in> set As - {A}\<close> \<open>a \<in> set (In B)\<close> apply (simp add: C In_CompA Out_out Comp_def Let_def In_Parallel set_diff set_addvars, auto)
            by (rule_tac x = A in bexI, simp_all)

          have [simp]: "[y \<leadsto> In A @ (In (Parallel_list (As \<ominus> [A])) \<ominus> [a])] oo Trs A \<parallel> [In (Parallel_list (As \<ominus> [A])) \<ominus> [a] \<leadsto> In (Parallel_list (As \<ominus> [A])) \<ominus> [a] ] oo
              [a # (In (Parallel_list (As \<ominus> [A])) \<ominus> [a]) \<leadsto> In (Parallel_list (As \<ominus> [A]))] oo
                Trs (Parallel_list (As \<ominus> [A])) oo [Out (Parallel_list As) \<ominus> [a] \<leadsto> z] = [y \<leadsto> In C] oo Trs C oo [Out C \<leadsto> z]"
               apply (simp add: C CompA_def Let_def Comp_def)
               apply (simp add: InAs'_def [THEN symmetric] Out_out par_empty_left)
               apply (subgoal_tac "[y \<leadsto> In A @ (InAs' \<ominus> [a])] oo Trs A \<parallel> [InAs' \<ominus> [a] \<leadsto> InAs' \<ominus> [a] ] oo [a # (InAs' \<ominus> [a]) \<leadsto> InAs'] oo Trs (Parallel_list (As \<ominus> [A])) = 
                  [y \<leadsto> In A \<oplus> (InAs' \<ominus> [a])] oo ([In A \<oplus> (InAs' \<ominus> [a]) \<leadsto> In A @ (InAs' \<ominus> [a])] oo Trs A \<parallel> [InAs' \<ominus> [a] \<leadsto> InAs' \<ominus> [a] ] oo [a # (InAs' \<ominus> [a]) \<leadsto> InAs'] oo Trs (Parallel_list (As \<ominus> [A])))")
               apply simp_all
               apply (simp add: comp_assoc [THEN sym])
               apply (subgoal_tac " [y \<leadsto> In A @ (InAs' \<ominus> [a])] = [y \<leadsto> In A \<oplus> (InAs' \<ominus> [a])] oo [In A \<oplus> (InAs' \<ominus> [a]) \<leadsto> In A @ (InAs' \<ominus> [a])]")
               apply (simp_all)
               by (subst switch_comp, simp_all)

          show "fb ([a # y \<leadsto> concat (map In As)] oo parallel_list (map Trs As) oo [OutAs \<leadsto> a # z]) = [y \<leadsto> In C] oo Trs C oo [Out C \<leadsto> z]"
            by (subst fb_CompA_aux [of _ A], simp_all, simp_all)
       qed

(*is "_\<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _  \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _  \<Longrightarrow> fb ?Ta = ?Tb"*)

      definition "Deterministic As = (\<forall> A \<in> set As . deterministic (Trs A))"

      lemma Deterministic_fb_out_less_step: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> a = out A \<Longrightarrow> Deterministic As \<Longrightarrow> Deterministic (fb_out_less_step a As)"
        apply (simp add: fb_out_less_step_def mem_get_comp_out mem_get_other_out fb_less_step_def Deterministic_def set_diff, safe)
        by (simp add: Type_OK_simp deterministic_CompA)

      lemma in_equiv_fb_fb_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow>
        FB_Var (Parallel_list As) = a # L \<Longrightarrow> Bs = fb_out_less_step a As 
        \<Longrightarrow>  in_equiv (FB (Parallel_list As)) (FB (Parallel_list Bs))"
        apply (frule FB_Var_fb_out_less_step, simp_all)
        apply (simp add: in_equiv_def)
        apply (simp add: FB_def Let_def FB_Var_def)
        apply (simp add: funpow_swap1)
        apply (cut_tac S = "([L @ (In (Parallel_list (fb_out_less_step a As)) \<ominus> L) \<leadsto> In (Parallel_list (fb_out_less_step a As))] oo
                  Trs (Parallel_list (fb_out_less_step a As)) oo
                  [Out (Parallel_list (fb_out_less_step a As)) \<leadsto> L @ (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L)])"
              and A = "[In (Parallel_list As) \<ominus> a # L \<leadsto> In (Parallel_list (fb_out_less_step a As)) \<ominus> L]"
              and tsa = "TVs L"
              and ts = "TVs (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L)"
            in fb_indep_left_a)
        apply (rule fbtype_aux, simp_all)
        apply (simp add: FB_Var_def)
        apply (rule_tac f = "fb ^^ length L" in arg_cong)
        proof -
          assume [simp]: "loop_free As"
          assume [simp]: "Type_OK As"
          assume [simp]: "Var (Parallel_list As) (Parallel_list As) = a # L"
          assume " Deterministic As"

          from this have aux: "a # L = Var (Parallel_list As) (Parallel_list As)"
            by simp

          have aa: "distinct (Var (Parallel_list As) (Parallel_list As))"
            apply (subgoal_tac "Type_OK As")
            apply (simp add: Type_OK_def Var_def Out_Parallel In_Parallel)
            by simp 

          have bb[simp]: "distinct (a # L)"
            apply (subgoal_tac "distinct (Var (Parallel_list As) (Parallel_list As))")
            apply simp
            by (simp only: aa)

          have [simp]: "distinct L"
            apply (subgoal_tac "distinct (a # L)")
            apply simp
            by (simp only: bb)

          have [simp]: "a \<notin> set L"
            apply (subgoal_tac "distinct (a # L)")
            apply simp
            by (simp only: bb)

          have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> type_ok A"
            apply (subgoal_tac "Type_OK As")
            apply (simp add: Type_OK_def)
            by simp

          have [simp]: "\<And> A . A \<in> set (fb_out_less_step a As) \<Longrightarrow> type_ok A"
            by (metis Type_OK_def FB_Var_def Type_OK_fb_out_less_step \<open>Type_OK As\<close> \<open>loop_free As\<close> aux)
           

          def InAs \<equiv> "In (Parallel_list As)"
          def InStAs \<equiv> " In (Parallel_list (fb_out_less_step a As))"

          def OutAs \<equiv> "Out (Parallel_list As)"
          def OutStAs \<equiv> "Out (Parallel_list (fb_out_less_step a As))"

          have [simp]: "distinct InAs"
            using InAs_def \<open>Type_OK As\<close> type_ok_def type_ok_parallel_list by blast

          have [simp]: " distinct (InAs \<ominus> a # L)"
            apply (subst distinct_diff)
            apply (simp add: InAs_def)
            using \<open>Type_OK As\<close> type_ok_def type_ok_parallel_list apply blast
            by simp

          have [simp]: "set L \<inter> set (InAs \<ominus> a # L) = {}"
            apply (simp add: set_diff)
            by blast

          have PermInAs[simp]: "perm (a # L @ (InAs \<ominus> a # L)) InAs"
            by (metis Var_def Cons_eq_appendI InAs_def \<open>Type_OK As\<close> aux diff_inter_right perm_switch_aux_f type_ok_def type_ok_parallel_list)


          obtain A where AAa[simp]: "A \<in> set As" and AAb: "a = out A"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "FB_Var (Parallel_list As) = a # L")
            apply (frule FB_Var_cons_out, auto)
            by (simp add: FB_Var_def)

          obtain B where AAc: "B \<in> set As" and AAd: "a \<in> set (In B)"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "FB_Var (Parallel_list As) = a # L")
            apply (frule FB_Var_cons_out_In)
            apply auto
            by (simp add: FB_Var_def)
         
          have [simp]: "B \<noteq> A"
            using AAa AAb AAd BBBB_f \<open>Type_OK As\<close> \<open>loop_free As\<close> by blast

          have [simp]: "length (Out A) = 1"
            using AAa Type_OK_simp \<open>Type_OK As\<close> by blast

          have [simp]:"out A \<in> set (In B)"
            using AAb AAd by auto

          have [simp]: "distinct InStAs"
            apply (simp add: InStAs_def)
            apply (subgoal_tac "type_ok (Parallel_list (fb_out_less_step a As))")
            using type_ok_def apply blast
            by (simp add: AAb Type_OK_fb_out_less_step_aux fb_out_less_step_def mem_get_comp_out mem_get_other_out type_ok_parallel_list)

          have AAe:"((\<Union>B\<in>set As. set (In B))) = {a} \<union>  set L \<union> ((\<Union>x\<in>set As. set (In x)) - insert (out A) (set L))"
            apply (cut_tac PermInAs)
            apply (subst (asm) distinct_perm_set_eq, simp_all)
            apply (simp add: set_diff)
            apply (simp add: InAs_def set_diff)
            apply (simp add: In_Parallel AAb)
              by auto


          have [simp]: "out A \<notin> set (In A)"
            using AAa BBBB_f \<open>Type_OK As\<close> \<open>loop_free As\<close> by blast

          have [simp]: "perm (L @ (InAs \<ominus> a # L)) InStAs"
            apply (rule set_perm, simp_all)
            apply (simp add: InAs_def InStAs_def set_diff)
            apply (simp add: In_Parallel)
            apply (simp add: fb_out_less_step_def mem_get_comp_out AAb mem_get_other_out fb_less_step_def)
            (*apply (simp add: set_diff)*)
            apply (cut_tac AAc)
            apply (cut_tac As = "As \<ominus> [A]" and A = A and B = B in union_set_In_CompA)
            apply simp_all
            apply (simp_all add: set_diff)
            apply (subgoal_tac "set (In A) \<union> ((\<Union>x\<in>set As - {A}. set (In x)) - {out A}) = (\<Union>x\<in>set As . set (In x)) - {out A}")
            apply simp
            apply (subst (2) AAe)
            apply safe [1]
            apply simp_all
            apply (simp add: AAb [THEN sym])
            apply (simp add: AAb)
            apply safe  
            apply simp_all
            apply (rule_tac x = A in bexI, simp_all)
            by auto

          have [simp]: "Var (Parallel_list (fb_out_less_step a As)) (Parallel_list (fb_out_less_step a As)) = L"
            by (metis FB_Var_def FB_Var_fb_out_less_step \<open>Type_OK As\<close> \<open>loop_free As\<close> aux)

          have [simp]: "perm (InAs \<ominus> a # L) (InStAs \<ominus> L)"
            apply (simp add: InAs_def InStAs_def)
            apply (cut_tac As = As and a  = a and L = L in perm_FB_Parallel, simp_all)
            apply (simp add: FB_Var_def)
            by (simp add: FB_def Let_def)

          have [simp]:  "set (InStAs \<ominus> L) \<subseteq> set (InAs \<ominus> a # L)"
            apply (subgoal_tac "perm (InStAs \<ominus> L) (InAs \<ominus> a # L)")
            by (simp_all add: perm_sym)


          have A: "ID (TVs L) \<parallel> [InAs \<ominus> a # L \<leadsto> InStAs \<ominus> L] oo [L @ (InStAs \<ominus> L) \<leadsto> InStAs] = [L @ (InAs \<ominus> a # L) \<leadsto> InStAs]"
            apply (simp add: distinct_id [THEN sym])
            apply (subst par_switch, simp_all)
            apply (subst switch_comp, simp_all add: perm_union_right)
            by (simp add: set_diff)

          thm fb_out_less_step_def
          thm fb_less_step_def

          thm InAs_def
          thm InStAs_def

          def C \<equiv> "CompA A (Parallel_list (As \<ominus> [A]))"

          thm fb_CompA [of As A a C OutAs "L @ (InAs \<ominus> a # L)" " L @ (OutAs \<ominus> a # L)" B]

          have [simp]: "Type_OK (As \<ominus> [A])"
            using \<open>Type_OK As\<close> 
            by (metis AAa Type_OK_def concat_map_Out_get_other_out distinct_diff inter_subset mem_get_other_out notin_inter)

          have "type_ok C"
            apply (simp add: C_def)
            apply (rule type_ok_CompA)
            using \<open>Type_OK As\<close>
            apply simp_all
            apply (rule type_ok_parallel_list)
            by simp

          have [simp]: "out A \<in> set (In (Parallel_list (As \<ominus> [A])))"
            apply (simp add: In_Parallel set_diff)
            using AAc \<open>B \<noteq> A\<close> \<open>out A \<in> set (In B)\<close> by blast

          have [simp]: "perm (L @ (InAs \<ominus> out A # L)) (In C)"
            apply (rule set_perm, simp_all)
            using AAb \<open>distinct (InAs \<ominus> a # L)\<close> \<open>distinct L\<close> \<open>set L \<inter> set (InAs \<ominus> a # L) = {}\<close> distinct_append apply blast
            using \<open>type_ok C\<close> apply (simp)
            apply (simp add: C_def CompA_def Comp_def Let_def Var_def)
            apply (simp add: C_def set_diff InAs_def In_Parallel Comp_def CompA_def set_addvars set_inter)
            apply (subgoal_tac "set (a # L) = set (Var (Parallel_list As) (Parallel_list As))")
            apply (simp add: Var_def Out_Parallel In_Parallel set_inter)
            apply auto [1]
            apply (simp_all add: Out_out)
            using AAb \<open>a \<notin> set L\<close> by blast
            

          have "set (a # L) = set (Var (Parallel_list As) (Parallel_list As))"
            by simp

          from this have [simp]: "perm (L @ (OutAs \<ominus> out A # L)) (Out C)"
            apply (simp add: Var_def Out_Parallel In_Parallel set_inter)
            apply (rule set_perm, simp, safe)
            using OutAs_def \<open>Type_OK As\<close> distinct_diff type_ok_def type_ok_parallel_list apply blast
            apply (simp add: set_diff)
            using \<open>type_ok C\<close> type_ok_def apply auto[1]
            apply (simp_all add: C_def Comp_def Let_def)
            apply (simp_all add: Out_Parallel Var_def set_diff set_inter OutAs_def Out_out)
            apply (safe, simp_all)
            apply (unfold set_eq_iff)
            apply (simp)
               apply (drule_tac x = x in spec, simp_all, safe)
                
            apply (rule_tac x = xa in bexI, auto)
            apply (simp_all add: Out_out)
            using AAb \<open>a \<notin> set L\<close> apply auto
            apply (rule_tac x = xa in bexI, auto)
            apply (simp_all add: Out_out)
            using \<open>Type_OK As\<close>
            apply (unfold Type_OK_simp, safe)
            apply (simp add: Out_out)
            by (metis AAa \<open>Type_OK As\<close> mem_get_comp_out)

          have Ub: "fb ([a # L @ (InAs \<ominus> a # L) \<leadsto> concat (map In As)] oo parallel_list (map Trs As) oo [OutAs \<leadsto> a # L @ (OutAs \<ominus> a # L)]) 
            = [L @ (InAs \<ominus> a # L) \<leadsto> In C] oo Trs C oo [Out C \<leadsto> L @ (OutAs \<ominus> a # L)]"
            apply (rule fb_CompA [of As A a C OutAs "L @ (InAs \<ominus> a # L)" " L @ (OutAs \<ominus> a # L)" B])
            apply (simp_all add: AAb)
            apply (simp add: C_def)
            apply (simp add: OutAs_def)
            using \<open>B \<in> set As\<close> by simp

          thm fb_less_step_compA [of A "(As \<ominus> [A])"]

          thm fb_CompA_aux [of As A a InAs OutAs "L @ (InAs \<ominus> a # L)" " L @ (OutAs \<ominus> a # L)" InStAs]
          thm fb_less_step_compA

          thm fb_out_less_step_def

          have Ua: "fb_out_less_step a As = fb_less_step A (As \<ominus> [A])"
            apply (simp add: fb_out_less_step_def)
            by (simp add: AAb mem_get_comp_out mem_get_other_out)

          def D \<equiv> "Parallel_list (fb_less_step A (As \<ominus> [A]))"

          have Va: "L @ (OutAs \<ominus> a # L) = L @ (OutStAs \<ominus> L)"
             using \<open>Type_OK As\<close> \<open>A \<in> set As\<close> \<open>a = out A\<close> apply (simp only: OutAs_def OutStAs_def Out_Parallel map_Out_fb_out_less_step mem_get_other_out)
             apply simp
             by (metis AAa \<open>Type_OK As\<close> concat_map_Out_get_other_out diff_cons mem_get_other_out)


          have [simp]: "Out A \<otimes> In (Parallel_list (As \<ominus> [A])) = [a]"
            using  \<open>a = out A\<close> by (simp add: Out_out)


          thm map_Out_fb_out_less_step
          have Vb: "Out C = OutStAs"
             using \<open>Type_OK As\<close> \<open>A \<in> set As\<close> \<open>a = out A\<close> apply (simp only: C_def OutStAs_def Out_Parallel )
             apply (subst map_Out_fb_out_less_step, simp_all)
             by (simp add: CompA_def Comp_def Let_def Var_def Out_out mem_get_other_out Out_Parallel)
          

          have Vc: "InStAs = In D"
            by (simp add: InStAs_def D_def Ua)

          have [simp]: "TI (Trs C) = TVs (In C)"
            by (metis AAa AAb C_def Type_OK_def Type_OK_fb_out_less_step_aux Ua \<open>Type_OK As\<close> inter_subset map_Out_fb_out_less_step mem_get_other_out notin_inter type_ok_CompA type_ok_def type_ok_parallel_list)
            

          have [simp]: "perm (L @ (InAs \<ominus> a # L)) (In D)"
            using Vc \<open>perm (L @ (InAs \<ominus> a # L)) InStAs\<close> by blast

          have [simp]: "distinct (In (Parallel_list As) \<ominus> a # L)"
            using InAs_def \<open>distinct (InAs \<ominus> a # L)\<close> by auto

          have [simp]: "perm (a # L @ (In (Parallel_list As) \<ominus> a # L)) (In (Parallel_list As))"
            using InAs_def PermInAs by blast

          have [simp]: "deterministic (Trs A)"
            using \<open>Deterministic As\<close> \<open>A \<in> set As\<close> by (simp add: Deterministic_def)


          have "in_equiv D C"
            apply (unfold C_def D_def)
            by (rule fb_less_step_compA [of A "As \<ominus> [A]"], simp_all)
            
          from this have Ud: "[L @ (InAs \<ominus> a # L) \<leadsto> In C] oo Trs C oo [Out C \<leadsto> L @ (OutAs \<ominus> a # L)] 
                  = [L @ (InAs \<ominus> a # L) \<leadsto> InStAs] oo Trs D oo [OutStAs \<leadsto> L @ (OutStAs \<ominus> L)]"
            apply (unfold in_equiv_def, simp add: Va Vb Vc, safe)
            apply (subst comp_assoc [THEN sym], simp_all)
            apply (subgoal_tac "[L @ (InAs \<ominus> a # L) \<leadsto> In C] = [L @ (InAs \<ominus> a # L) \<leadsto> In D] oo [In D \<leadsto> In C]", simp_all)
            by (subst switch_comp, simp_all)

          have Uc: "fb ([a # L @ (InAs \<ominus> a # L) \<leadsto>  concat (map In As)] oo parallel_list (map Trs As) oo [OutAs \<leadsto> a # L @ (OutAs \<ominus> a # L)]) 
            = fb ([a # L @ (InAs \<ominus> a # L) \<leadsto> InAs] oo Trs (Parallel_list As) oo [OutAs \<leadsto> a # L @ (OutAs \<ominus> a # L)])"
            apply (simp add: Trs_Parallel_list)
            apply (simp add:  comp_assoc [THEN sym] InAs_def TI_parallel_list)
            apply (subgoal_tac "[a # L @ (In (Parallel_list As) \<ominus> a # L) \<leadsto> concat (map In As)] = [a # L @ (In (Parallel_list As) \<ominus> a # L) \<leadsto> In (Parallel_list As)] oo [In (Parallel_list As) \<leadsto> concat (map In As)]")
            apply simp_all
            apply (subst switch_comp, simp_all, safe)
            apply (simp_all add: set_diff)
            by (simp add: In_Parallel, auto)


          from Ub Uc Ud have "fb ([a # L @ (InAs \<ominus> a # L) \<leadsto> InAs] oo Trs (Parallel_list As) oo [OutAs \<leadsto> a # L @ (OutAs \<ominus> a # L)]) =
                [L @ (InAs \<ominus> a # L) \<leadsto> InStAs] oo Trs (Parallel_list (fb_less_step A (As \<ominus> [A]))) oo [OutStAs \<leadsto> L @ (OutStAs \<ominus> L)]"
            by (simp add: D_def)
          

          from Ua and this have B: "fb ([a # L @ (InAs \<ominus> a # L) \<leadsto> InAs] oo Trs (Parallel_list As) oo [OutAs \<leadsto> a # L @ (OutAs \<ominus> a # L)]) =
                [L @ (InAs \<ominus> a # L) \<leadsto> InStAs] oo Trs (Parallel_list (fb_out_less_step a As)) oo [OutStAs \<leadsto> L @ (OutStAs \<ominus> L)]"
           by simp

          have [simp]: "Type_OK (fb_out_less_step a As)"
            by (metis FB_Var_def Type_OK_fb_out_less_step \<open>Type_OK As\<close> \<open>Var (Parallel_list As) (Parallel_list As) = a # L\<close> \<open>loop_free As\<close>)

          have "fb ([a # L @ (InAs \<ominus> a # L) \<leadsto> InAs] oo Trs (Parallel_list As) oo [OutAs \<leadsto> a # L @ (OutAs \<ominus> a # L)]) =
               ID (TVs L) \<parallel> [InAs \<ominus> a # L \<leadsto> InStAs \<ominus> L] oo 
               ([L @ (InStAs \<ominus> L) \<leadsto> InStAs] oo Trs (Parallel_list (fb_out_less_step a As)) oo [OutStAs \<leadsto> L @ (OutStAs \<ominus> L)])"
            apply (subst B)
            apply (subst A [THEN sym])
            apply (subst comp_assoc, simp_all)
            apply (simp add: TI_Parallel_list InStAs_def In_Parallel)
            apply (subst comp_assoc, simp_all)
            apply (subst TI_comp, simp_all)
            apply (simp add: TI_Parallel_list InStAs_def In_Parallel)
            apply (subst TO_comp, simp_all)
            apply (simp add: TI_Parallel_list InStAs_def In_Parallel)
            by (simp add: TO_Parallel_list OutStAs_def Out_Parallel)

          from this show "fb ([a # L @ (In (Parallel_list As) \<ominus> a # L) \<leadsto> In (Parallel_list As)] oo Trs (Parallel_list As) 
                            oo [Out (Parallel_list As) \<leadsto> a # L @ (Out (Parallel_list As) \<ominus> a # L)]) =
                         ID (TVs L) \<parallel> [In (Parallel_list As) \<ominus> a # L \<leadsto> In (Parallel_list (fb_out_less_step a As)) \<ominus> L] oo
                            ([L @ (In (Parallel_list (fb_out_less_step a As)) \<ominus> L) \<leadsto> In (Parallel_list (fb_out_less_step a As))] oo Trs (Parallel_list (fb_out_less_step a As)) oo
                            [Out (Parallel_list (fb_out_less_step a As)) \<leadsto> L @ (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L)])"
            by (simp add: InAs_def OutAs_def InStAs_def OutStAs_def)
       qed
      

      lemma type_ok_FB_Parallel_list: "Type_OK As \<Longrightarrow> type_ok (FB (Parallel_list As))"
        by (simp_all add:  Type_ok_FB type_ok_parallel_list)


      lemma [simp]: "type_ok A \<Longrightarrow> \<lparr>In = In A, Out = Out A, Trs =  Trs A\<rparr> = A"
        by auto

      thm loop_free_def

      lemma io_rel_compA: "length (Out A) = 1 \<Longrightarrow> io_rel (CompA A B) \<subseteq> io_rel B \<union> (io_rel B O io_rel A)"
        apply (simp add: CompA_def, safe)
        apply (simp add: Comp_def Let_def io_rel_def  set_addvars set_diff Var_def set_inter relcomp_def OO_def out_def)
        by (case_tac "Out A", simp_all)

      theorem loop_free_fb_out_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A = a \<Longrightarrow> loop_free (fb_out_less_step a As)"
        proof (rule ccontr)
          assume D: "loop_free As"
          assume "Type_OK As"
          assume [simp]: "A \<in> set As"
          assume "out A = a"

          have [simp]: "fb_out_less_step a As = map (CompA A) (As \<ominus> [A])"
            apply (simp add: fb_out_less_step_def fb_less_step_def)
            by (metis \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_comp_out mem_get_other_out)

          assume "\<not> loop_free (fb_out_less_step a As)"

          from this obtain x where C: "(x,x) \<in> (IO_Rel (map (CompA A) (As \<ominus> [A])))\<^sup>+"
            by (simp add: loop_free_def, blast)

          have A: "\<And> B . B \<in> set As \<Longrightarrow> io_rel B \<subseteq> (IO_Rel As)\<^sup>+"
            apply (rule_tac y = "IO_Rel As" in order_trans)
            apply (simp add: io_rel_def IO_Rel_def)
             apply auto
             by (simp add: io_rel_def, auto)

          have B: "\<And> A B . A \<in> set As \<Longrightarrow> B \<in> set As \<Longrightarrow> io_rel B O io_rel A \<subseteq> (IO_Rel As)\<^sup>+"
            apply (rule_tac y = "(IO_Rel As)\<^sup>+ O (IO_Rel As)\<^sup>+" in order_trans)
            apply (simp add: A relcomp_mono)
            apply safe
            by (rule_tac y = y in trancl_trans, simp_all)

          have "\<And> B . B \<in> set As \<Longrightarrow> io_rel (CompA A B) \<subseteq> (IO_Rel As)\<^sup>+"
            apply (rule_tac y = "io_rel B \<union> (io_rel B O io_rel A)" in order_trans)
            apply (rule io_rel_compA)
            using Type_OK_def \<open>A \<in> set As\<close> \<open>Type_OK As\<close> apply blast
            apply safe
            apply (cut_tac A) apply auto

            apply (subgoal_tac " io_rel B O io_rel A \<subseteq> (IO_Rel As)\<^sup>+")
            apply auto [1]
            by (rule B, simp_all)

          from this have "IO_Rel (map (CompA A) (As \<ominus> [A])) \<subseteq> (IO_Rel As)\<^sup>+"
            apply (subst IO_Rel_def, safe)
            by (simp add: io_rel_def image_def set_diff, safe, auto)

            thm r_r_into_trancl

            thm trancl_trans

          from this have "(IO_Rel (map (CompA A) (As \<ominus> [A])))\<^sup>+ \<subseteq> (IO_Rel As)\<^sup>+"
            apply (rule trancl_Int_subset, safe)
            apply (rule_tac y = y in  trancl_trans )
            apply blast
            by blast

          from this and C and D show "False"
            by (simp add: loop_free_def, auto)
       qed

      theorem "\<And> As . Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = L \<Longrightarrow>  
                  in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As)) \<and> type_ok (Parallel_list (fb_less L As))"
        apply (induction L)
        apply (frule type_ok_parallel_list)
        apply (simp add: FB_def FB_Var_def diff_emptyset)
        apply (rule in_equiv_eq, simp, simp)
        proof -
          fix a:: 'var
          fix L :: "'var list"
          fix As:: "('var, 'a) Dgr list"
          assume A: "(\<And>As ::('var, 'a) Dgr list. Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = L \<Longrightarrow> in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As)) \<and> type_ok (Parallel_list (fb_less L As)))"
          assume [simp]: "loop_free As"
          assume [simp]: "Type_OK As"
          assume [simp]: "FB_Var (Parallel_list As) = a # L"
          assume [simp]: "Deterministic As"
  
          def Bs \<equiv> "fb_out_less_step a As"
  
          from this have Bs_simp: "Bs = fb_out_less_step a As"
            by simp

          obtain A where AAa[simp]: "A \<in> set As" and AAb: "a = out A"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "FB_Var (Parallel_list As) = a # L")
            by (frule FB_Var_cons_out, auto)
  
          from AAb have [simp]: "Deterministic Bs"
            apply (simp only: Bs_simp)
            by (rule_tac A = A in  Deterministic_fb_out_less_step, simp_all)
  
          have [simp]: "loop_free Bs"
            apply (simp only: Bs_simp)
            by (rule_tac A = A and As = As in loop_free_fb_out_less_step, simp_all add: AAb)
  
          have [simp]: "Type_OK Bs"
            using Bs_def Type_OK_fb_out_less_step \<open>FB_Var (Parallel_list As) = a # L\<close> \<open>Type_OK As\<close> \<open>loop_free As\<close> by blast
  
          from A have Aa: "(\<And>As ::('var, 'a) Dgr list. Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = L \<Longrightarrow> in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As)))"
            by simp
  
          from A have Ab: "(\<And>As ::('var, 'a) Dgr list. Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> FB_Var (Parallel_list As) = L \<Longrightarrow>  type_ok (Parallel_list (fb_less L As)))"
            by simp
  
  
          have [simp]: "FB_Var (Parallel_list Bs) = L"
            apply (simp add: Bs_def)
            by (rule FB_Var_fb_out_less_step, simp_all)
  
          have [simp]: "in_equiv (FB (Parallel_list Bs)) (Parallel_list (fb_less L Bs))"
            by (rule Aa, simp_all)
  
  
          have [simp]: "type_ok (Parallel_list (fb_less L Bs))"
            by (rule Ab, simp_all)
  
          have [simp]: "in_equiv (FB (Parallel_list As)) (FB (Parallel_list Bs))"
            apply (rule in_equiv_fb_fb_less_step, simp_all)
            by (simp add: Bs_def)
 
          show "in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less (a # L) As))  \<and> type_ok (Parallel_list (fb_less (a # L) As))"
            apply (simp add: Bs_simp [THEN sym])
            apply (rule_tac B = "FB (Parallel_list Bs)" in in_equiv_tran)
            by (simp_all add: type_ok_FB_Parallel_list)
        qed

end

end