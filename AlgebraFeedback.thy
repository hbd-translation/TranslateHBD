section{*Abstract Algebra of  Hierarchical Block Diagrams with all axioms*}

theory AlgebraFeedback imports AlgebraFeedbackless
begin
  
locale BaseOperation = BaseOperationFeedbackless +
  assumes fb_twice_switch_no_vars: "TI S = t' # t # ts \<Longrightarrow> TO S = t' # t # ts'
      \<Longrightarrow> (fb ^^ (2::nat)) (Switch [t] [t'] \<parallel> ID ts oo S oo Switch [t'] [t] \<parallel> ID ts') = (fb ^^ (2:: nat)) S"
    
      
locale BaseOperationVars = BaseOperation + BaseOperationFeedbacklessVars
begin
lemma fb_twice_switch: "distinct (a # b # x) \<Longrightarrow> distinct (a # b # y) \<Longrightarrow> TI S = TVs (b # a # x) \<Longrightarrow> TO S = TVs (b # a # y) 
      \<Longrightarrow> (fb ^^ (2::nat)) ([a # b # x \<leadsto> b # a # x] oo S oo [b # a # y \<leadsto> a # b # y]) = (fb ^^ (2:: nat)) S"
  apply (cut_tac S = S  and t = "TV a" and t' = "TV b" and ts = "TVs x" in fb_twice_switch_no_vars, simp_all add: distinct_id sw_hd_var)
  by (subst sw_hd_var, auto)

lemma fb_switch_a: "\<And> S . distinct (a # z @ x) \<Longrightarrow> distinct (a # z @ y) \<Longrightarrow> TI S = TVs (z @ a # x) \<Longrightarrow> TO S = TVs (z @ a # y) 
      \<Longrightarrow> (fb ^^ (Suc (length z))) ([a # z @ x \<leadsto> z @ a # x] oo S oo [z @ a # y \<leadsto> a # z @ y]) = (fb ^^ (Suc (length z))) S"
proof (induction z)
  case Nil
  from Nil show ?case
    by simp_all
next
        case (Cons b z)

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
          using Cons by (subst par_switch, auto , subst par_switch, auto)
        also have "... = (fb ^^ length z) (fb (fb ([[b] \<leadsto> [b]] \<parallel> [a # z @ x \<leadsto> z @ a # x] oo S oo [[b] \<leadsto> [b]] \<parallel> [z @ a # y \<leadsto> a # z @ y])))"
          by (simp add: numeral_2_eq_2 del: )
        also have "... = (fb ^^ length z) (fb ([a # z @ x \<leadsto> z @ a # x] oo fb S oo  [z @ a # y \<leadsto> a # z @ y]))"
          by (simp add: Cons.prems(3) Cons.prems(4) distinct_id fb_comp)
        also have "... = (fb ^^ Suc (length z)) ([a # z @ x \<leadsto> z @ a # x] oo fb S oo  [z @ a # y \<leadsto> a # z @ y])"
          by (simp add: funpow_add funpow_swap1)
        also have "... = (fb ^^ Suc (length z))  (fb S)"
          using Cons by (subst Cons(1), simp_all add: TI_fb_fbtype TO_fb_fbtype fbtype_def TVs_def)
        also have "... = (fb ^^ Suc (length (a # z))) S"
          by (simp add: funpow_add funpow_swap1)
        finally show ?case by simp
      qed

      lemma swap_power: "(f ^^ n) ((f ^^ m) S) = (f ^^ m) ((f ^^ n) S)"
        by (metis add.left_commute funpow_add funpow_simps_right(1) o_apply o_id)

          
      lemma fb_switch_b: "\<And> v x y S . distinct (u @ v @ x) \<Longrightarrow> distinct (u @ v @ y) \<Longrightarrow> TI S = TVs (v @ u @ x) \<Longrightarrow> TO S = TVs (v @ u @ y) 
      \<Longrightarrow> (fb ^^ (length (u @ v))) ([u @ v @ x \<leadsto> v @ u @ x] oo S oo [v @ u @ y \<leadsto> u @ v @ y]) = (fb ^^ (length (u @ v))) S"
        proof (induction u)
        case Nil
          show ?case
            using Nil by simp_all
        next
        case (Cons a u)
          have "(fb ^^ length (a # u @ v)) ([a # u @ v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # u @ v @ y])
              =  (fb ^^ length v) ((fb ^^ (Suc (length u)))([a # u @ v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # u @ v @ y]))"
            apply (simp add: funpow_add funpow_swap1)
            by (rule swap_power)
          also have "... = (fb ^^ length v) ((fb ^^ (Suc (length u))) (
            [a # u @ v @ x \<leadsto> u @ a # v @ x] oo ([u @ a # v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> u @ a # v @ y]) oo [u @ a # v @ y \<leadsto> a # u @ v @ y]))"
            using Cons apply (simp add: comp_assoc switch_comp_a)
              
            apply (subst switch_comp_a)
                apply simp_all
              apply blast
             apply blast
             apply (simp add: comp_assoc [THEN sym])
            by (subst switch_comp_a, auto)

          also have "... = (fb ^^ length v) ((fb ^^ Suc (length u)) ([u @ a # v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> u @ a # v @ y]))"
            using Cons by (subst fb_switch_a, simp_all)

          also have "... = (fb ^^ (length (u @ (a # v)))) ([u @ a # v @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> u @ a # v @ y])"
            apply (simp add: funpow_add funpow_swap1)
            by (rule swap_power)
          also have "... =  (fb ^^ (length (u @ (a # v)))) ([u @ (a # v) @ x \<leadsto> (a # v) @ u @ x] 
              oo ([(a # v) @ u @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> (a # v) @ u @ y])
              oo [(a # v) @ u @ y \<leadsto> u @ (a # v) @ y])"
            using Cons(4) Cons(5)
            apply (simp add: comp_assoc)
            using Cons(3) apply (subst switch_comp_a, simp_all)
               apply blast
              apply blast
              apply blast
            apply (simp add: comp_assoc [THEN sym])
            using Cons(2) by (subst switch_comp_a, simp_all, auto)

          also have "... = (fb ^^ length (u @ a # v)) ([a # v @ u @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # v @ u @ y])"
            using Cons by (subst Cons(1), simp_all)
          also have "... = (fb ^^ length u) (((fb ^^ (Suc (length v)))) ([a # v @ u @ x \<leadsto> v @ a # u @ x] oo S oo [v @ a # u @ y \<leadsto> a # v @ u @ y]))"
            by (simp add: funpow_add funpow_swap1)
          also have "... =  (fb ^^ length u) ((fb ^^ Suc (length v)) S)"
            using Cons by (subst fb_switch_a, simp_all, blast, blast)
          also have "... = (fb ^^ length ((a # u) @ v)) S"
            by (simp add: funpow_add funpow_swap1)
 
          finally show ?case
            by simp
        qed
          
    theorem fb_perm: "\<And> v S . perm u v \<Longrightarrow> distinct (u @ x) \<Longrightarrow> distinct (u @ y) \<Longrightarrow> fbtype S (TVs u) (TVs x) (TVs y) 
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
            by (metis perm_length \<open>u <~~> w @ w'\<close> length_append)

          have [simp]: "set u = set w \<union> set w'"
            by (metis Permutation.perm_set_eq \<open>u <~~> w @ w'\<close> set_append)

          have [simp]: "distinct w" and [simp]:"distinct w'"
            apply (meson Cons.prems(3) \<open>perm u (w @ w')\<close> dist_perm distinct.simps(2) distinct_append)
            by (meson Cons.prems(3) \<open>perm u (w @ w')\<close> dist_perm distinct.simps(2) distinct_append)

          have A: "set w \<inter> set w' = {}"
            by (meson Cons.prems(3) \<open>perm u (w @ w')\<close> dist_perm distinct.simps(2) distinct_append)

          have "(fb ^^ length (a # u)) ([v @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> v @ y]) 
            = (fb ^^ length w') ((fb ^^ (length (w @ [a]))) ([w @ a # w' @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> w @ a # w' @ y]))"
            apply (simp add: funpow_add funpow_swap1)
            using \<open>v = w @ a # w'\<close> swap_power by fastforce
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
            
            using A Cons apply (subst fb_switch_b, simp_all add: fbtype_def)
            apply blast
            by blast

          also have "... = (fb ^^ length u) (fb ([a # w @ w' @ x \<leadsto> a # u @ x] oo S oo [a # u @ y \<leadsto> a # w @ w' @ y]))"
            apply (simp add: funpow_add funpow_swap1)
            using \<open>v = w @ a # w'\<close> swap_power by fastforce
          also have "... = (fb ^^ length u) (fb ([[a] \<leadsto> [a]] \<parallel> [w @ w' @ x \<leadsto> u @ x] oo S oo [[a] \<leadsto> [a]] \<parallel> [u @ y \<leadsto> w @ w' @ y]))"
            using A Cons 
            apply (subst par_switch, simp_all add: fbtype_def TVs_def)
            apply blast
              apply blast
            apply (subst par_switch)
               apply simp_all
              by blast
          also have "... = (fb ^^ length u) ([(w @ w') @ x \<leadsto> u @ x] oo fb S oo [u @ y \<leadsto> (w @ w') @ y])"
            using Cons apply simp
            
            by (simp add: distinct_id fb_comp fbtype_def)
 
          also have "... = (fb ^^ length u) (fb S)"
            using A Cons by (subst Cons(1), simp_all add: fbtype_def TI_fb_fbtype TO_fb_fbtype)

          also have "... = (fb ^^ length (a # u)) S"
            by (simp add: funpow_add funpow_swap1)
          finally show ?case
            by (simp)
        qed     

end

  
end