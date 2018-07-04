section{*Diagrams with Named Inputs and Outputs*}

(* Was: DiagramFeedbackless.thy *)

theory Diagrams imports HBDAlgebra
begin 
  
text{*This file contains the definition and properties for the named input output diagrams*}
  

record ('var, 'a) Dgr = 
    In:: "'var list"
    Out:: "'var list"
    Trs:: 'a
    
context BaseOperationFeedbacklessVars
begin
definition "Var A B = (Out A) \<otimes> (In B)"

definition "io_diagram A = (TVs (In A) = TI (Trs A) \<and> TVs (Out A) = TO (Trs A) \<and> distinct (In A) \<and> distinct (Out A))"

definition  Comp :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr"  (infixl ";;" 70) where
  "A ;; B = (let I = In B \<ominus> Var A B in let O' = Out A \<ominus> Var A B in
    \<lparr>In = (In A) \<oplus> I, Out = O' @ Out B, 
    Trs = [(In A) \<oplus> I \<leadsto> In A @ I ] oo Trs A \<parallel> [I \<leadsto> I] oo [Out A @ I \<leadsto> O' @ In B]  oo ([O' \<leadsto> O'] \<parallel> Trs B) \<rparr>)"

lemma io_diagram_Comp: "io_diagram A \<Longrightarrow> io_diagram B
        \<Longrightarrow> set (Out A \<ominus> In B) \<inter> set (Out B) = {} \<Longrightarrow> io_diagram (A ;; B)"
  by (auto simp add: io_diagram_def Comp_def Let_def Var_def addvars_def set_diff set_inter)
        
lemma Comp_in_disjoint: 
  assumes "io_diagram A"
    and "io_diagram B"
    and "set (In A) \<inter> set (In B) = {}"
    shows "A ;; B = (let I = In B \<ominus> Var A B in let O' = Out A \<ominus> Var A B in
      \<lparr>In = (In A) @ I, Out = O' @ Out B, Trs = Trs A \<parallel> [I \<leadsto> I] oo [Out A @ I \<leadsto> O' @ In B]  oo ([O' \<leadsto> O'] \<parallel> Trs B) \<rparr>)"
proof -
  have [simp]: "In A \<oplus> (In B \<ominus> Var A B) = In A @ (In B \<ominus> Var A B)"
    by (metis addvars_def assms(3) diff_emptyset diff_inter_right empty_inter_diff)
  have [simp]: "[In A @ (In B \<ominus> Var A B) \<leadsto> In A @ (In B \<ominus> Var A B)] = ID (TVs (In A) @ TVs (In B \<ominus> Var A B))"
    apply (subst distinct_id, simp_all)
    by (metis \<open>In A \<oplus> (In B \<ominus> Var A B) = In A @ (In B \<ominus> Var A B)\<close> assms(1) assms(2) distinct_addvars distinct_append distinct_diff io_diagram_def)
      
  have [simp]: "TI (Trs A) = TVs (In A)"
    using assms(1) io_diagram_def by force       
  show ?thesis
    by (simp add: Comp_def Let_def)
qed

lemma Comp_full: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> Out A = In B \<Longrightarrow>
  A ;; B = \<lparr>In = In A, Out = Out B, Trs = Trs A oo Trs B \<rparr>"
  by (simp_all add: Comp_def Let_def Var_def io_diagram_def diff_inter_left diff_eq addvars_def  par_empty_left par_empty_right)

lemma Comp_in_out: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (Out A) \<subseteq> set (In B) \<Longrightarrow>
  A ;; B = (let I = diff (In B) (Var A B) in let O' = diff (Out A) (Var A B) in
          \<lparr>In = In A \<oplus> I, Out = Out B, Trs = [In A \<oplus> I \<leadsto> In A @ I ] oo Trs A \<parallel> [I \<leadsto> I] oo [Out A @ I \<leadsto> In B] oo Trs B \<rparr>)"
  by (simp add: Comp_def Let_def Var_def diff_inter_left diff_inter_right diff_subset par_empty_left)

  
lemma Comp_assoc_new: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow>
          set (Out A \<ominus> In B) \<inter> set (Out B) = {} \<Longrightarrow>  set (Out A \<otimes> In B) \<inter> set (In C) = {}
          \<Longrightarrow> A ;; B ;; C = A ;; (B ;; C)"
proof -
            assume [simp]: "io_diagram A"
            assume [simp]: "io_diagram B"
            assume [simp]: "io_diagram C"
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

          define x where "x \<equiv> In A"
          define u where "u \<equiv> Out A"
          define y where "y \<equiv> In B"
          define v where "v \<equiv> Out B"
          define z where "z \<equiv> In C"
          define w where "w \<equiv> Out C"

          have [simp]: "TI (Trs A) = TVs x"
            by (metis \<open>io_diagram A\<close> io_diagram_def x_def)

          have [simp]: "TI (Trs B) = TVs y"
            by (metis \<open>io_diagram B\<close> io_diagram_def y_def)

          have [simp]: "TO (Trs A) = TVs u"
            by (metis \<open>io_diagram A\<close> io_diagram_def u_def)

          have [simp]: "distinct x"
           by (metis \<open>io_diagram A\<close> io_diagram_def x_def)

          have [simp]: "distinct u"
           by (metis \<open>io_diagram A\<close> io_diagram_def u_def)

          have [simp]: "distinct y"
           by (metis \<open>io_diagram B\<close> io_diagram_def y_def)

          have [simp]: "distinct z"
           by (metis \<open>io_diagram C\<close> io_diagram_def z_def)

          have [simp]: "distinct (z \<ominus> (u \<ominus> u \<otimes> y) @ v \<otimes> z)"
            by (simp add: )

          have [simp]: "distinct (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))"
            by (simp add: distinct_addvars )

          have [simp]: "distinct (x \<oplus> (y \<ominus> u \<otimes> y))"
            by (simp add: distinct_addvars )

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
            by (simp add: distinct_addvars )
            
          have [simp]: "set u \<inter> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) = {}"
            by (simp add: set_diff set_inter set_addvars, auto)
            
          have [simp]: "distinct (y \<oplus> (z \<ominus> v \<otimes> z))"
            by (simp add: distinct_addvars )
            
          have [simp]: "set (u \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))) \<subseteq> set u \<union> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))"
            by (simp add: set_diff set_inter set_addvars, auto)
          have [simp]: "set (y \<oplus> (z \<ominus> v \<otimes> z)) \<subseteq> set u \<union> set (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z)))"
            by (simp add: set_diff set_inter set_addvars, auto)
          have [simp]: "set y \<subseteq> set (y \<oplus> (z \<ominus> v \<otimes> z))"
            by (simp add: set_diff set_inter set_addvars)
            
          have [simp]: "set (z \<ominus> v \<otimes> z) \<subseteq> set (y \<oplus> (z \<ominus> v \<otimes> z))"
            by (simp add: set_diff set_inter set_addvars)

          have [simp]: "TO (Trs B) = TVs v"
            by (metis \<open>io_diagram B\<close> io_diagram_def v_def)
          have [simp]: " TI (Trs C) = TVs z"
            by (metis \<open>io_diagram C\<close> io_diagram_def z_def)

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
            by (simp add: diff_inter_left diff_inter_right)

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


          define z' where "z' \<equiv> newvars (y \<ominus> u) (TVs (z \<ominus> (u \<ominus> y) @ v))"

          have [simp]: "distinct (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u))"
            by (metis \<open>distinct (x \<oplus> (y \<oplus> (z \<ominus> v \<otimes> z) \<ominus> u \<otimes> (y \<oplus> (z \<ominus> v \<otimes> z))))\<close> diff_inter_right)
          have "distinct (y \<ominus> u)"
            by (simp add: )

          have [simp]: "distinct z'"
            by (simp add: z'_def)

          have [simp]: "set (y \<ominus> u) \<inter> set z' = {}"
            by (simp add: z'_def)

          have [simp]: "distinct (y \<oplus> (z \<ominus> v) \<ominus> u)"
            by (simp add:  distinct_addvars)

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
            by (simp add: )

          have H: "Trs A \<parallel> [y \<ominus> u \<leadsto> y \<ominus> u] \<parallel> [z \<ominus> (u \<ominus> y) @ v \<leadsto> z \<ominus> (u \<ominus> y) @ v] = Trs A \<parallel> [(y \<ominus> u) @ z' \<leadsto> (y \<ominus> u) @ z']"
            by (simp add: par_assoc distinct_id)

          define u' where "u' \<equiv> newvars (x @ y @ z @ v) (TVs u)"

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
              by (simp add: par_assoc distinct_id)
            also have "... = [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ ((y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v))]"
              by (simp add: par_switch)
            finally show ?thesis by simp
            qed
       
          have Hb: "[u \<leadsto> u] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> y \<oplus> (z \<ominus> v) \<ominus> u] = [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ (y \<oplus> (z \<ominus> v) \<ominus> u)]"
            proof -
            have "[u \<leadsto> u] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> y \<oplus> (z \<ominus> v) \<ominus> u] = [u' \<leadsto> u'] \<parallel> [x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u) \<leadsto> y \<oplus> (z \<ominus> v) \<ominus> u]"
              by (simp add: par_assoc distinct_id)
            also have "... =  [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ (y \<oplus> (z \<ominus> v) \<ominus> u)]"
              by (simp add: par_switch)
            finally show ?thesis by simp
            qed

         have [simp]: " Subst (z \<ominus> (u \<ominus> y) @ v) (z \<ominus> (u \<ominus> y) @ v) (z \<ominus> (u \<ominus> y) @ v) = (z \<ominus> (u \<ominus> y) @ v)"
          by (simp add: Subst_eq)

         have [simp]: "Subst (u @ (y \<ominus> u)) (u' @ (y \<ominus> u)) ((u \<ominus> y) @ y) = Subst u u' (u \<ominus> y) @ Subst u u' y"
          apply (simp add: Subst_append, safe)
          apply (subst Subst_cancel_left, simp_all)
          apply (rule TVs_length_eq, simp)
          apply (subst Subst_cancel_left, simp_all)
          by (rule TVs_length_eq, simp)
        
         have Hc: "[u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> u' @ (y \<ominus> u) @ (z \<ominus> (u \<ominus> y) @ v)] oo [u @ (y \<ominus> u) \<leadsto> (u \<ominus> y) @ y] \<parallel> [z \<ominus> (u \<ominus> y) @ v \<leadsto> z \<ominus> (u \<ominus> y) @ v]
          = [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> Subst u u' (u \<ominus> y) @ Subst u u' y @ (z \<ominus> (u \<ominus> y) @ v)]"
            apply (subst append_assoc [THEN sym])
            apply (subst switch_par_comp_Subst, simp_all)
            apply (simp_all add: set_diff set_addvars )
            apply auto
            using  V  by (auto simp add: set_inter set_diff u_def y_def x_def v_def z_def) [1]

         have [simp]: "Subst (u @ (y \<oplus> (z \<ominus> v) \<ominus> u)) (u' @ (y \<oplus> (z \<ominus> v) \<ominus> u)) ((u \<ominus> y \<oplus> (z \<ominus> v)) @ y @ (z \<ominus> v)) 
            = Subst u  u' ((u \<ominus> y \<oplus> (z \<ominus> v)) @ y @ (z \<ominus> v))"
          apply (subst Subst_cancel_left, simp_all)
          by (rule TVs_length_eq, simp)

         thm par_switch_eq_a

         have J: "[u \<ominus> (y \<oplus> (z \<ominus> v)) \<leadsto> u \<ominus> (y \<oplus> (z \<ominus> v))] \<parallel> [v \<ominus> z \<leadsto> v \<ominus> z] =  [(u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z) \<leadsto> (u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z)]"
          apply (subst par_switch, simp_all, safe)
          using \<open>io_diagram B\<close> distinct_diff io_diagram_def v_def apply blast
          apply (simp add: set_diff set_addvars set_inter, auto)
          using U by (auto simp add: set_inter set_diff u_def y_def v_def z_def) [1]

         have [simp]: "distinct v"
          using \<open>io_diagram B\<close> io_diagram_def v_def by blast

         have [simp]: "distinct (z \<ominus> v)"
          by (simp add: )

         have [simp]: "distinct (u \<ominus> y)"
          by (simp add: )

         have [simp]: "distinct (u \<ominus> (y \<oplus> (z \<ominus> v)))"
          by (simp add: )

          have [simp]: "length u' = length u"
            by (rule TVs_length_eq, simp)

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

         define v' where "v' \<equiv> newvars (u' @ u @ x @ y @ z) (TVs v)"  

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
          by (rule TVs_length_eq, simp)

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

      from a have [simp]: "set v' \<inter> set (z \<ominus> v) = {}"
        by (simp add: set_diff set_addvars, auto)

      from a have [simp]: " set v' \<inter> set (u \<ominus> y \<ominus> v) = {}"
       by  (simp add: set_diff set_addvars, auto)

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
        apply (subst Subst_comp, simp_all)
        apply (simp add: set_diff)
        apply auto [1]
        apply (subst Comp_assoc_new_subst_aux [of _ y], simp_all)

        apply (subst Subst_switch, simp_all)
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
 
         have I: "[u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> Subst u u' (u \<ominus> y) @ Subst u u' y @ (z \<ominus> (u \<ominus> y) @ v)] oo [u \<ominus> y \<leadsto> u \<ominus> y] \<parallel> Trs B \<parallel> [z \<ominus> (u \<ominus> y) @ v \<leadsto> z \<ominus> (u \<ominus> y) @ v] oo
            [(u \<ominus> y) @ v @ (z \<ominus> (u \<ominus> y) @ v) \<leadsto> (u \<ominus> (y \<oplus> (z \<ominus> v))) @ (v \<ominus> z) @ z]
             =
            [u' @ (x \<oplus> (y \<oplus> (z \<ominus> v) \<ominus> u)) \<leadsto> Subst u u' (u \<ominus> (y \<oplus> (z \<ominus> v))) @ Subst u u' y @ Subst u u' (z \<ominus> v)] oo [u \<ominus> (y \<oplus> (z \<ominus> v)) \<leadsto> u \<ominus> (y \<oplus> (z \<ominus> v))] \<parallel> Trs B \<parallel> [z \<ominus> v \<leadsto> z \<ominus> v] oo
            [u \<ominus> (y \<oplus> (z \<ominus> v)) \<leadsto> u \<ominus> (y \<oplus> (z \<ominus> v))] \<parallel> [v @ (z \<ominus> v) \<leadsto> (v \<ominus> z) @ z]"
          apply (rule_tac v = v' in par_switch_eq_a, simp_all add:  )
           apply (subst switch_comp_subst, simp_all) 
             (*
          apply (simp add: set_diff)
          using U  apply (simp add: v_def u_def z_def y_def set_diff set_inter set_addvars)*)
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

    lemma Comp_assoc_a: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow>
          set (In B) \<inter> set (In C) = {} \<Longrightarrow>
          set (Out A) \<inter> set (Out B) = {} \<Longrightarrow>
          A ;; B ;; C = A ;; (B ;; C)"
        apply (rule Comp_assoc_new, simp_all)
         apply (metis diff.simps(1) inter_diff_distrib set_empty2 set_inter)
        by (simp add: inf_assoc set_inter)

    (*to do too many conditions in next, replace with the theorem above*)
(*
    lemma Comp_assoc: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow>
          set (In A) \<inter> set (In B) = {} \<Longrightarrow> set (In B) \<inter> set (In C) = {} \<Longrightarrow> set (In A) \<inter> set (In C) = {} \<Longrightarrow>
          set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> set (Out B) \<inter> set (Out C) = {} \<Longrightarrow> set (Out A) \<inter> set (Out C) = {} \<Longrightarrow>
          A ;; B ;; C = A ;; (B ;; C)"
      apply (rule Comp_assoc_new)
          apply simp
         apply simp
        apply simp
         apply (metis diff.simps(1) inter_diff_distrib set_empty2 set_inter)
        by (simp add: inf_assoc set_inter)
*)

definition Parallel :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr"  (infixl "|||" 80) where
   "A ||| B = \<lparr>In = In A \<oplus> In B, Out = Out A @ Out B, Trs = [In A \<oplus> In B \<leadsto> In A @ In B] oo (Trs A \<parallel> Trs B) \<rparr>"
       

      lemma io_diagram_Parallel: "io_diagram A \<Longrightarrow> io_diagram B  \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> io_diagram (A ||| B)"
        by (simp add: io_diagram_def Parallel_def   distinct_addvars)

 
      lemma Parallel_indep: "io_diagram A \<Longrightarrow> io_diagram B  \<Longrightarrow> set (In A) \<inter> set (In B) = {} \<Longrightarrow>
        A ||| B = \<lparr>In = In A @ In B, Out = Out A @ Out B, Trs = (Trs A \<parallel> Trs B) \<rparr>"
        apply (simp add: Parallel_def, safe)
        apply (simp add: addvars_def diff_distinct)
        apply (subgoal_tac "In A \<oplus> In B = In A @ In B")
        apply simp
        apply (subst distinct_id)
        apply (simp add: io_diagram_def)
        apply (subst comp_id_left_simp)
        apply (simp add: io_diagram_def)
        apply simp
        by (simp add: addvars_def diff_distinct)


      lemma Parallel_assoc_gen: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> 
            A ||| B ||| C = A ||| (B ||| C)"
        proof -
          assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"
          assume [simp]: "io_diagram C"

          have [simp]: "TVs (In A) = TI (Trs A)"
            apply (subgoal_tac "io_diagram A")
            apply (simp only: io_diagram_def)
            by simp

          have [simp]: "distinct (In A)"
            apply (subgoal_tac "io_diagram A")
            apply (simp only: io_diagram_def)
            by simp

          have [simp]: "TVs (In B) = TI (Trs B)"
            apply (subgoal_tac "io_diagram B")
            apply (simp only: io_diagram_def)
            by simp

          have [simp]: "distinct (In B)"
            apply (subgoal_tac "io_diagram B")
            apply (simp only: io_diagram_def)
            by simp

          have [simp]: "TVs (In C) = TI (Trs C)"
            apply (subgoal_tac "io_diagram C")
            apply (simp only: io_diagram_def)
            by simp

          have [simp]: "distinct (In C)"
            apply (subgoal_tac "io_diagram C")
            apply (simp only: io_diagram_def)
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
        
definition "VarFB A = Var A A"
definition "InFB A= In A \<ominus> VarFB A"
definition "OutFB A = Out A \<ominus> VarFB A"

definition FB :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr" where
  "FB A = (let I = In A \<ominus> Var A A in let O' = Out A \<ominus> Var A A in
      \<lparr>In = I, Out = O', Trs = (fb ^^ (length (Var A A))) ([Var A A @ I \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ O']) \<rparr>)"


lemma Type_ok_FB: "io_diagram A \<Longrightarrow> io_diagram (FB A)"
        apply (simp add: io_diagram_def FB_def Let_def Var_def, safe)
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
        by (simp add: length_TVs)

lemma perm_var_Par: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (In A) \<inter> set (In B) = {} 
  \<Longrightarrow> perm (Var (A ||| B) (A ||| B)) (Var A A @ Var B B @ Var A B @ Var B A)"
        apply (simp add: Parallel_indep Var_def append_inter)
        apply (frule_tac x = "Out A" in inter_append)
        apply (drule_tac x = "Out B" in inter_append)
        by (simp add: perm_mset union_commute union_lcomm)

      lemma distinct_Parallel_Var[simp]: "io_diagram A \<Longrightarrow> io_diagram B  
        \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> distinct (Var (A ||| B) (A ||| B))"
        apply (simp add: Parallel_def Var_def append_inter, safe)
        apply (simp add:  io_diagram_def)
         apply (simp add:  io_diagram_def)
        by (metis IntI notin_inter)

      lemma distinct_Parallel_In[simp]: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> distinct (In (A ||| B))"
        apply (simp add: Parallel_def Var_def append_inter io_diagram_def)
        using distinct_addvars by auto

      lemma drop_assumption: "p \<Longrightarrow> True"
        by simp


(*
New proof
      theorem FP_IC_res_new: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (In A) \<inter> set (In B) = {} 
      \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> FB (A ||| B) = FB (FB (A) ;; FB (B))"
        proof -
          assume A [simp]: "set (In A) \<inter> set (In B) = {}"
          assume B [simp]: "set (Out A) \<inter> set (Out B) = {}"
          have [simp]: "In A \<oplus> In B = In A @ In B"
            by (simp add: addvars_distinct)
          assume "io_diagram A"
          assume "io_diagram B"
          have [simp]: "distinct (In A)" and [simp]: "distinct (In B)"
            using \<open>io_diagram A\<close> io_diagram_def apply auto[1]
            using \<open>io_diagram B\<close> io_diagram_def by auto[1]
          have [simp]: "TI (Trs A) = TVs (In A)" and "TO (Trs A) = TVs (Out A)"
            using \<open>io_diagram A\<close> io_diagram_def apply force
            using \<open>io_diagram A\<close> io_diagram_def by force
          have [simp]: "TI (Trs B) = TVs (In B)" and "TO (Trs B) = TVs (Out B)"
            using \<open>io_diagram B\<close> io_diagram_def apply force
            using \<open>io_diagram B\<close> io_diagram_def by force

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


      lemma Var_FB[simp]: "Var (FB A) (FB A) = []"
        by (simp add: FB_def Var_def Let_def)

      theorem FB_idemp: "io_diagram A \<Longrightarrow> FB (FB A) = FB A"
        apply (subst FB_def)
        apply (simp add: Let_def diff_emptyset)
        apply (rule Dgr_eq, simp_all)
        by (metis (no_types, lifting) io_diagram_def  Type_ok_FB comp_id_right comp_id_switch distinct_id)

    definition VarSwitch :: "'var list \<Rightarrow> 'var list \<Rightarrow> ('var, 'a) Dgr" ("[[_ \<leadsto> _]]") where
      "VarSwitch x y = \<lparr>In = x, Out = y, Trs = [x \<leadsto> y]\<rparr>"
      

      definition "in_equiv  A B = (perm (In A) (In B) \<and> Trs A = [In A \<leadsto> In B] oo Trs B \<and> Out A  = Out B)"
      definition "out_equiv A B = (perm (Out A) (Out B) \<and> Trs A = Trs B oo [Out B \<leadsto> Out A] \<and> In A = In B)"

      definition "in_out_equiv A B = (perm (In A) (In B) \<and> perm (Out A) (Out B) \<and> Trs A = [In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A])"

      lemma in_equiv_io_diagram: "in_equiv A B \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram A"
        apply (simp add: io_diagram_def in_equiv_def, safe)
        using dist_perm perm_sym by blast

      lemma in_out_equiv_io_diagram: "in_out_equiv A B \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram A"
        apply (simp add: io_diagram_def in_out_equiv_def, safe)
        using dist_perm perm_sym apply blast
        using dist_perm perm_sym by blast

      lemma in_equiv_sym: "io_diagram B \<Longrightarrow> in_equiv A B \<Longrightarrow> in_equiv B A"
        by (auto simp add: in_equiv_def perm_sym  comp_assoc[THEN sym] io_diagram_def switch_comp )
      
      lemma in_equiv_eq: "io_diagram A \<Longrightarrow> A = B \<Longrightarrow> in_equiv A B"
        by (simp add: in_equiv_def perm_mset io_diagram_def)

      lemma [simp]: "io_diagram A \<Longrightarrow> [In A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Out A] = Trs A"
        by (simp add: io_diagram_def)

      lemma in_equiv_tran: "io_diagram C \<Longrightarrow> in_equiv A B \<Longrightarrow> in_equiv B C \<Longrightarrow> in_equiv A C"
        apply (subgoal_tac "io_diagram B")
        apply (subgoal_tac "io_diagram A")
        apply (simp add: in_equiv_def)
        apply (simp_all add: in_equiv_io_diagram)
        apply (cut_tac x="In A" and y="In B" and z="In C" in  perm_trans)
        apply simp_all
        apply (subst comp_assoc [THEN sym])
        apply simp_all
        apply (unfold io_diagram_def, simp_all)
        apply (subst switch_comp)
           apply simp
          apply simp
         apply simp
          by simp

    lemma in_out_equiv_refl: "io_diagram A \<Longrightarrow> in_out_equiv A A"
      by (simp add: in_out_equiv_def perm_mset)

    lemma in_out_equiv_sym: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> in_out_equiv A B \<Longrightarrow> in_out_equiv B A"
      apply (simp add: in_out_equiv_def, safe)
      apply (simp add: perm_mset)
      apply (simp add: perm_mset)
      apply (simp add: io_diagram_def)
      apply (simp add: comp_assoc)
      apply (subgoal_tac "[Out B \<leadsto> Out A] oo [Out A \<leadsto> Out B] = ID (TVs (Out B))")
      apply simp_all
      apply (simp add: comp_assoc [THEN sym])
      apply (subgoal_tac "[In B \<leadsto> In A] oo [In A \<leadsto> In B] =  ID (TVs (In B))")
      apply simp_all
      apply (simp add: distinct_vars_comp perm_sym)
      by (simp add: distinct_vars_comp perm_sym)

    lemma in_out_equiv_tran: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> in_out_equiv A B \<Longrightarrow> in_out_equiv B C \<Longrightarrow> in_out_equiv A C"
      apply (simp add: in_out_equiv_def, safe)
      apply (simp add: perm_mset)
      apply (simp add: perm_mset)
      apply (unfold io_diagram_def, safe)
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


    lemma [simp]: "distinct (Out A) \<Longrightarrow> distinct (Var A B)"
      by (simp add: Var_def)

    lemma [simp]: "set (Var A B) \<subseteq> set (Out A)"
      by (auto simp add: Var_def set_inter)
    lemma [simp]: "set (Var A B) \<subseteq> set (In B)"
      by (auto simp add: Var_def set_inter)



    lemmas fb_indep_sym = fb_indep [THEN sym]

declare length_TVs [simp] 
  
  end
  

  primrec op_list :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow>'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
    "op_list e opr [] = e" |
    "op_list e opr (a # x) = opr a (op_list e opr x)"

primrec inter_set :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "inter_set [] X = []" |
  "inter_set (x # xs) X = (if x \<in> X then x # inter_set xs X else inter_set xs X)"

lemma list_inter_set: "x \<otimes> y = inter_set x (set y)"
      by (induction x, simp_all)

fun map2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool" where
  "map2 f [] [] = True" |
  "map2 f (a # x) (b # y) = (f a b \<and> map2 f x y)" |
  "map2 _ _ _ = False"
  
thm map_def
  
context BaseOperationFeedbacklessVars
begin
definition ParallelId :: "('var, 'a) Dgr" ("\<box>")
  where "\<box> =  \<lparr>In = [], Out = [], Trs = ID []\<rparr>"
    
lemma [simp]: "Out \<box> = []"
  by (simp add: ParallelId_def)

lemma [simp]: "In \<box> = []"
  by (simp add: ParallelId_def)

lemma [simp]: "Trs \<box> = ID []"
  by (simp add: ParallelId_def)
    
lemma ParallelId_right[simp]: "io_diagram A \<Longrightarrow> A ||| \<box> = A"
  apply (simp add: Parallel_def ParallelId_def)
  apply (subst comp_id_switch)
    apply (simp add: io_diagram_def)
   apply (simp add: io_diagram_def)
  apply (cut_tac x="[]" in  distinct_id)
   apply simp
  apply (subgoal_tac "TVs [] = []")
  using par_empty_right apply auto[1]
  by (simp add: TVs_def)

lemma ParallelId_left: "io_diagram A \<Longrightarrow> \<box> ||| A = A"
  apply (simp add: Parallel_def ParallelId_def)
  apply (subst comp_id_switch)
  by (simp_all add: io_diagram_def)

definition "parallel_list = op_list (ID []) (op \<parallel>)"
  
definition "Parallel_list = op_list \<box> (op |||)"
  
lemma [simp]: "Parallel_list [] = \<box>"
  by (simp add: Parallel_list_def)

definition "io_distinct As = (distinct (concat (map In As)) \<and> distinct (concat (map Out As)) \<and> (\<forall> A \<in> set As . io_diagram A))"
       
definition "io_rel A = set (Out A) \<times> set (In A)"

definition "IO_Rel As = \<Union> (set (map io_rel As))"

definition "out A = hd (Out A)" (*the first output of A*)

definition "Type_OK As = ((\<forall> B \<in> set As . io_diagram B \<and> length (Out B) = 1) 
                    \<and> distinct (concat (map Out As)))"

      lemma concat_map_out: "(\<forall> A \<in> set As . length (Out A) = 1) \<Longrightarrow> concat (map Out As) = map out As"
        apply (induction As, simp_all)
        apply (case_tac "Out a", simp_all)
        by (simp add: out_def)

      lemma Type_OK_simp: "Type_OK As =  ((\<forall> B \<in> set As . io_diagram B \<and> length (Out B) = 1) \<and> distinct (map out As))"
        apply (simp add: Type_OK_def, safe)
        by (simp_all add: concat_map_out)

      definition "single_out A = (io_diagram A \<and> length (Out A) = 1)"


definition CompA :: "('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr \<Rightarrow> ('var, 'a) Dgr" (infixl "\<rhd>" 75) where
(*  "A \<rhd> B = (if set(Out A) \<subseteq> set (In B) then A ;; B else B)"*)
  "A \<rhd> B = (if out A \<in> set (In B) then A ;; B else B)"

  
definition "internal As = {x . (\<exists> A \<in> set As . \<exists> B \<in> set As . x \<in> set (Out A) \<and> x \<in> set (In B))}"


primrec get_comp_out :: "'var \<Rightarrow> ('var, 'a) Dgr list \<Rightarrow> ('var, 'a) Dgr" where
    "get_comp_out x [] = \<lparr>In = [x], Out = [x], Trs = [ [x] \<leadsto> [x] ]\<rparr>" | (*can be undefined also. Using identity to be more convenient*)
    "get_comp_out x (A # As) = (if x \<in> set (Out A) then A else get_comp_out x As)" 
        

primrec get_other_out :: "'c \<Rightarrow> ('c, 'd) Dgr list \<Rightarrow> ('c, 'd) Dgr list" where
    "get_other_out x [] = []" |
    "get_other_out x (A # As) = (if x \<in> set (Out A) then get_other_out x As else A # get_other_out x As)"
    
      (*we assume the A is not in As*)
definition "fb_less_step A As = map (CompA A) As" 

      
definition "fb_out_less_step x As = fb_less_step (get_comp_out x As) (get_other_out x As)"

primrec fb_less :: "'var list \<Rightarrow> ('var, 'a) Dgr list \<Rightarrow> ('var, 'a) Dgr list" where
      "fb_less [] As = As" |
      "fb_less (x # xs) As = fb_less xs (fb_out_less_step x As)"
  

lemma [simp]: "VarFB \<box> = []"
  by (simp add: VarFB_def Var_def)
lemma [simp]: "InFB \<box> = []"
  by (simp add: VarFB_def Var_def InFB_def)
lemma [simp]: "OutFB \<box> = []"
  by (simp add: VarFB_def Var_def OutFB_def)
    

      definition "loop_free As = (\<forall> x . (x,x) \<notin> (IO_Rel As)\<^sup>+)"

lemma [simp]: "Parallel_list (A # As) = (A ||| Parallel_list As)"
  by (simp add: Parallel_list_def)

lemma [simp]: "Out (A ||| B) = Out A @ Out B"
  by (simp add: Parallel_def)

lemma [simp]: "In (A ||| B) = In A \<oplus> In B"
  by (simp add: Parallel_def)

lemma Type_OK_cons: "Type_OK (A # As) = (io_diagram A \<and> length (Out A) = 1 \<and> set (Out A) \<inter> (\<Union>a\<in>set As. set (Out a)) = {} \<and> Type_OK As)"
  by (simp add: Type_OK_def io_diagram_def, auto)

    
lemma Out_Parallel: "Out (Parallel_list As) = concat (map Out As)"
  by (induction As, simp_all)

      lemma internal_cons: "internal (A # As) = {x. x \<in> set (Out A) \<and> (x \<in> set (In A) \<or> (\<exists>B\<in>set As. x \<in> set (In B)))} \<union> {x . (\<exists>Aa\<in>set As. x \<in> set (Out Aa) \<and> (x \<in> set (In A)))}
          \<union> internal As"
        by (auto simp add: internal_def)
          
      lemma Out_out: "length (Out A) = Suc 0 \<Longrightarrow> Out A = [out A]"
        apply (simp add: out_def)
        by (case_tac "Out A", simp_all)

      lemma Type_OK_out: "Type_OK As \<Longrightarrow> A \<in> set As  \<Longrightarrow> Out A = [out A]"
        apply (simp add: out_def Type_OK_def)
        by (case_tac "Out A", simp_all, auto)


      lemma In_Parallel: "In (Parallel_list As) = op_list [] (op \<oplus>) (map In As)"
        by (induction As, simp_all)

      lemma [simp]: "set (op_list [] op \<oplus> xs) = \<Union> set (map set xs)"
        apply (induction xs, simp_all)
        by (simp add: set_addvars)

      lemma internal_VarFB: "Type_OK As \<Longrightarrow> internal As = set (VarFB (Parallel_list As))"
        apply (induction As)
        apply (simp add: VarFB_def Var_def internal_def Parallel_list_def ParallelId_def)
        apply (subgoal_tac "Out a = [out a]")
        apply (simp add: Type_OK_cons VarFB_def Var_def set_inter set_addvars internal_cons Type_OK_out Out_Parallel, safe)
        apply (simp_all add: Type_OK_out subsetset_inter)
        apply (rule_tac x = Aa in bexI)
        apply (simp add: Type_OK_out, simp)
        apply (rule_tac x = xa in bexI)
        apply (simp add: Type_OK_out, simp)
        apply blast
        apply blast
        apply blast
        apply auto
        by (simp_all add: In_Parallel)


      lemma map_Out_fb_less_step: "length (Out A) = 1 \<Longrightarrow>  map Out (fb_less_step A As) = map Out As"
        apply (induction As)
        apply (simp_all add: fb_less_step_def CompA_def Comp_def Let_def Var_def diff_inter_left, safe)
        by (case_tac "Out A", simp_all add: out_def)

      lemma mem_get_comp_out: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> get_comp_out (out A) As = A"
        apply (induction As, simp, auto)
         apply (simp add: Type_OK_def, auto)
          apply (metis (no_types, lifting) Out_out   list.set_intros(1))
         apply (simp add: Type_OK_def Out_out)
        prefer 2
        using Type_OK_cons apply blast
        proof -
          fix a :: "('var, 'a) Dgr" and Asa :: "('var, 'a) Dgr list"
          assume a1: "io_diagram a \<and> length (Out a) = Suc 0 \<and> (\<forall>B\<in>set Asa. io_diagram B \<and> length (Out B) = Suc 0) \<and> distinct (Out a) \<and> distinct (concat (map Out Asa)) \<and> set (Out a) \<inter> (\<Union>a\<in>set Asa. set (Out a)) = {}"
          assume a2: "A \<in> set Asa"
          assume "out A = out a"
          then have "\<not> distinct (map out (a # Asa))"
            using a2 by (metis (no_types) distinct.simps(2) image_eqI list.map(2) set_map)
          then show "a = A"
            using a1 by (metis (no_types) One_nat_def Type_OK_cons Type_OK_def Type_OK_simp)
        qed
 
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
          using Out_out apply force
        apply (simp add: fb_out_less_step_def)
           apply (subst map_Out_fb_less_step, simp_all)
            
            using Type_OK_cons apply auto[1]
            apply (simp add: Type_OK_cons)
              by (simp add: Type_OK_simp fb_out_less_step_def map_Out_fb_less_step mem_get_comp_out)


lemma [simp]: "Type_OK (A # As) \<Longrightarrow> Type_OK As"
        by (simp add: Type_OK_cons)

      lemma Type_OK_Out: "Type_OK (A # As) \<Longrightarrow> Out A = [out A]"
        by (rule Type_OK_out, simp_all, auto)

      lemma  concat_map_Out_get_other_out: "Type_OK As \<Longrightarrow> concat (map Out (get_other_out a As)) = (concat (map Out As) \<ominus> [a])"
        apply (induction As, simp_all)
        by (simp_all add: union_diff Type_OK_Out)
      thm Out_out
      lemma VarFB_cons_out: "Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = a # L \<Longrightarrow> \<exists> A \<in> set As . out A = a"
        apply (cut_tac As = As in internal_VarFB, simp_all)
        apply (simp add: internal_def)
        apply (unfold set_eq_iff)
        apply (drule_tac x = a in spec, simp_all add: Out_out, safe)
        apply (subst (asm) Out_out)
         apply (simp add: Type_OK_def)
        by auto
          


      lemma VarFB_cons_out_In: "Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = a # L \<Longrightarrow> \<exists> B \<in> set As . a \<in> set (In B)"
        apply (cut_tac As = As in internal_VarFB, simp_all)
        apply (simp add: internal_def)
        apply (unfold set_eq_iff)
        by (drule_tac x = a in spec, simp_all)


      (*todo: find better names to next lemmas*)
      lemma AAA_a: "Type_OK (A # As) \<Longrightarrow> A \<notin> set As"
        apply (simp add: Type_OK_def, auto)
        by (case_tac "Out A", simp_all, auto)


      lemma AAA_b: "(\<forall> A \<in> set As. a \<notin> set (Out A)) \<Longrightarrow> get_other_out a As = As"
        by (induction As, simp_all)

     
      lemma AAA_d: "Type_OK (A # As) \<Longrightarrow> \<forall>Aa\<in>set As. out A \<noteq> out Aa"
        apply (simp add: Type_OK_def)
        apply (unfold set_eq_iff)
        apply (case_tac "Out A", simp_all, safe)
        apply (drule_tac x = "a" in spec, safe, auto)
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
          
        using Type_OK_cons apply blast
          
           apply (simp add: Type_OK_Out)
          
        using Type_OK_cons apply blast
          
         apply (simp add: Out_out Type_OK_simp)
        using AAA_a by blast

(*
lemma In_CompA: "In (A \<rhd> B) = (if set (Out A) \<subseteq> set (In B) then In A \<oplus> (In B \<ominus> Out A) else In B)"
  by (simp add: CompA_def Comp_def Let_def Var_def diff_inter_right)
*)

lemma In_CompA: "In (A \<rhd> B) = (if out A \<in> set (In B) then In A \<oplus> (In B \<ominus> Out A) else In B)"
  by (simp add: CompA_def Comp_def Let_def Var_def diff_inter_right)
      
  
lemma union_set_In_CompA: "\<And> B . length (Out A) = 1 \<Longrightarrow> B \<in> set As \<Longrightarrow> out A \<in> set (In B) 
    \<Longrightarrow> (\<Union>x\<in>set As. set (In (CompA A x))) = set (In A) \<union> ((\<Union> B \<in> set As . set (In B)) - {out A})"
  proof (induction As)
    case Nil
    then show ?case by simp
  next
    case (Cons a As)
    have [simp]: "out A \<in> set (In B)"
      by (simp add: Cons.prems(3))
    have [simp]: "Out A = [out A]"
      by (simp add: Cons.prems(1) Out_out)
    show ?case
      proof (cases "\<forall> C \<in> set As . out A \<notin> set (In C)")
        case True
        have [simp]: "a = B"
          using Cons.prems(2) Cons.prems(3) True by auto
        from True show ?thesis
          by (auto simp add:  In_CompA set_addvars set_diff)
      next
        case False
        from this obtain C where [simp]: "C \<in> set As" and [simp]: "out A \<in> set (In C)"
          by blast
        show ?thesis
          apply simp
          apply (subst Cons(1) [of C])
          by (auto simp add:  In_CompA set_addvars set_diff)
      qed
    qed

lemma BBBB_e: "Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = out A # L \<Longrightarrow> A \<in> set As \<Longrightarrow> out A \<notin> set L"
  apply (simp add: VarFB_def Var_def Out_Parallel Type_OK_def, safe)
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
        
lemma [simp]: "x \<in> set (Out (get_comp_out x As))"
  by (induction As, auto simp add: out_def)

lemma comp_out_in: "A \<in> set As \<Longrightarrow> a \<in> set (Out A) \<Longrightarrow> (get_comp_out a As) \<in> set As"
  apply (induction As, simp)
  by auto
    
lemma  [simp]: "a \<in> internal As \<Longrightarrow> get_comp_out a As \<in> set As"
  apply (simp_all add: internal_def)
   using comp_out_in by blast
    
lemma out_CompA: "length (Out A) = 1 \<Longrightarrow> out (CompA A B) = out B"
  apply (simp add: CompA_def)
  apply (simp add: Comp_def Let_def Var_def out_def)
  by (case_tac "Out A", simp_all)
    
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
    
      lemma BBB_a: "length (Out A) = 1 \<Longrightarrow> Out (CompA A B) = Out B"
        apply (simp add: CompA_def, safe)
        apply (simp add: Comp_def Let_def Var_def diff_inter_left out_def)
        by (case_tac "Out A", simp_all)

      lemma BBB_b: "length (Out A) = 1 \<Longrightarrow> map (Out \<circ> CompA A) As = map Out As"
        apply (induction As, simp_all)
        by (simp add: BBB_a)
  
lemma VarFB_fb_out_less_step_gen:
  assumes "loop_free As"
    assumes "Type_OK As"
    and internal_a: "a \<in> internal As"
    shows "VarFB (Parallel_list (fb_out_less_step a As)) = (VarFB (Parallel_list As)) \<ominus> [a]"
proof -
  define A where "A = get_comp_out a As"
  have [simp]: "A \<in> set As"
    using A_def internal_a by auto [1]
      
  from this have "length (Out A) = 1"
    using \<open>Type_OK As\<close> by (unfold Type_OK_def, simp) 
  from this have "Out A = [out A]"
    by (simp add: Out_out)
      
  have "a \<in> set (Out A)"
    by (simp add: \<open>A \<equiv> get_comp_out a As\<close>)
      
  have Out_a: "out A = a"
    using \<open>Out A = [out A]\<close> \<open>a \<in> set (Out A)\<close> by auto
      
  have [simp]: "get_other_out a As = As \<ominus> [A]"
    using Out_a \<open>A \<in> set As\<close> assms(2) mem_get_other_out by blast
      
  from internal_a obtain C where [simp]: "C \<in> set As" and [simp]: "a \<in> set (In C)" and [simp]: "C \<noteq> A"
    apply (unfold internal_def, safe)
    by (metis Out_a Type_OK_loop_free_elem assms(1) assms(2))
      
  have a_not_in_A: "a \<notin> set (In A)"
    using BBBB_f Out_a \<open>A \<in> set As\<close> assms(1) assms(2) by blast
 
  have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> Out A = [out A]"
    using Type_OK_out assms(2) by blast

  have [simp]: "concat (map Out (As \<ominus> [A])) = (concat (map Out As) \<ominus> [a])"
    by (metis \<open>get_other_out a As = As \<ominus> [A]\<close> assms(2) concat_map_Out_get_other_out)
      
  have [simp]: "UNION (set (As \<ominus> [A])) (set \<circ> (In \<circ> CompA A)) = set (op_list [] op \<oplus> (map In As) \<ominus> [a])"
    apply (simp add: set_diff, simp, safe)
      apply (case_tac "out A \<in> set (In xa)")
       apply (simp add: CompA_def Comp_def Let_def set_addvars set_diff)
       apply auto[2]
     apply (case_tac "out A \<in> set (In xa)")
      apply (simp add: CompA_def Comp_def Let_def set_addvars set_diff)
      apply (simp add: a_not_in_A Var_def)
    using CompA_def apply auto[1]
    apply (case_tac "a \<in> set (In xa)", simp_all)
       apply (simp add: Out_a CompA_def Comp_def Let_def set_addvars set_diff)
      apply (simp add: Out_a Var_def a_not_in_A)
       apply (simp add: Out_a CompA_def Comp_def Let_def set_addvars set_diff)
    apply (case_tac "xa = A", simp_all)
     apply (drule_tac x = C in bspec)
      apply simp_all
     apply (simp add: CompA_def Comp_def Let_def set_addvars set_diff Out_a)
    apply (drule_tac x = xa in bspec, simp)
      apply (case_tac "a \<in> set (In xa)")
     by (simp_all add: CompA_def Comp_def Let_def set_addvars set_diff Out_a Var_def)
      
  show "VarFB (Parallel_list (fb_out_less_step a As)) = (VarFB (Parallel_list As)) \<ominus> [a]"
    apply (simp add: VarFB_def Var_def Out_Parallel In_Parallel fb_out_less_step_def A_def [THEN sym] fb_less_step_def)
    apply (subst BBB_b, simp_all)
    apply (simp add: listinter_diff)
    apply (rule set_listinter)
    by simp
qed
  
thm internal_VarFB
thm VarFB_fb_out_less_step_gen
  

lemma VarFB_fb_out_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = a # L \<Longrightarrow> VarFB (Parallel_list (fb_out_less_step a As)) = L"
  apply (subst VarFB_fb_out_less_step_gen, simp_all)
   apply (simp add: internal_VarFB)
  apply (subgoal_tac "distinct (VarFB (Parallel_list As))")
   apply (metis AAA_c distinct.simps(2))
  by (metis Out_Parallel Type_OK_def VarFB_def Var_def distinct_inter)
    
                
lemma Parallel_list_cons:"Parallel_list (a # As) = a ||| Parallel_list As"
  by simp

lemma io_diagram_parallel_list: "Type_OK As \<Longrightarrow> io_diagram (Parallel_list As)"
        apply (induction As)
        apply (simp add: ParallelId_def io_diagram_def)
        apply (simp only: Parallel_list_cons)
        apply (subst io_diagram_Parallel)
        by (simp_all add: Type_OK_def Out_Parallel)

      lemma BBB_c: "distinct (map f As) \<Longrightarrow> distinct (map f (As \<ominus> Bs))"
        by (induction As, simp_all add: image_def set_diff)

      lemma io_diagram_CompA: "io_diagram A \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram (CompA A B)"
        apply (simp add: CompA_def, safe)
        apply (subst Comp_in_out)
           apply simp_all

        using Out_out apply fastforce
        by (simp add: Let_def Var_def diff_inter_left diff_inter_right io_diagram_def addvars_def set_diff)


      lemma Type_OK_fb_out_less_step_aux: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow>  Type_OK (fb_less_step A (As \<ominus> [A]))"
        apply (unfold fb_less_step_def)
        apply (subst Type_OK_def, safe, simp_all add: image_def, safe)
        apply (subst io_diagram_CompA, simp_all)
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

    
          
      thm VarFB_cons_out
        
theorem Type_OK_fb_out_less_step_new: "Type_OK As \<Longrightarrow>
      a \<in> internal As \<Longrightarrow>
      Bs = fb_out_less_step a As \<Longrightarrow> Type_OK Bs"
  apply (simp add: internal_def, safe)
  apply (simp add: fb_out_less_step_def)
    apply (subgoal_tac "Out A = [out A]", simp) 
  apply (subgoal_tac "(get_comp_out (out A) As) = A", simp_all)
  apply (subgoal_tac "get_other_out (out A) As = (As \<ominus> [A])", simp_all)
  apply (rule Type_OK_fb_out_less_step_aux, simp_all)
  using mem_get_other_out apply blast
  using mem_get_comp_out apply blast
  by (simp add: Type_OK_def Out_out)
    
theorem Type_OK_fb_out_less_step: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow>
        VarFB (Parallel_list As) = a # L \<Longrightarrow> Bs = fb_out_less_step a As \<Longrightarrow> Type_OK Bs"
  apply (rule Type_OK_fb_out_less_step_new, simp_all)
  by (simp add: internal_VarFB)


lemma perm_FB_Parallel[simp]: "loop_free As \<Longrightarrow> Type_OK As
      \<Longrightarrow> VarFB (Parallel_list As) = a # L \<Longrightarrow> Bs = fb_out_less_step a As 
      \<Longrightarrow> perm (In (FB (Parallel_list As))) (In (FB (Parallel_list Bs)))"
  apply (frule VarFB_cons_out, simp_all, safe)
  apply (frule VarFB_cons_out_In, simp_all, safe)
  apply (rule set_perm)
    apply (drule io_diagram_parallel_list)
        apply (drule Type_ok_FB)
        apply (simp add: io_diagram_def)
        apply (frule Type_OK_fb_out_less_step, simp_all)
        apply (drule_tac As = "(fb_out_less_step (out A) As)" in io_diagram_parallel_list)
        apply (drule Type_ok_FB)
        apply (simp add: io_diagram_def)
        apply (frule VarFB_fb_out_less_step, simp_all)
        apply (simp add: FB_def Let_def In_Parallel )
        apply (simp add: VarFB_def)
        apply (simp add: set_diff fb_out_less_step_def fb_less_step_def)
        apply (simp add: mem_get_other_out mem_get_comp_out)
        apply (subst union_set_In_CompA, simp_all)
        apply (simp add: Type_OK_def)
        apply (simp add: set_diff)
         apply (rule BBBB_f, simp_all)
        apply (simp add: set_diff)
        apply (unfold set_eq_iff, auto)
        by (simp add: Type_OK_loop_free_elem)


      lemma [simp]: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow>
          VarFB (Parallel_list As) = a # L \<Longrightarrow>  
          Out (FB (Parallel_list (fb_out_less_step a As))) = Out (FB (Parallel_list As))"
        apply (frule VarFB_cons_out, simp_all, safe)
        apply (frule VarFB_fb_out_less_step, simp_all)
        apply (simp add: FB_def Let_def VarFB_def)
        apply (simp add: Out_Parallel)
        apply (subst map_Out_fb_out_less_step, simp_all)
        apply (simp add: concat_map_Out_get_other_out)
        by (metis diff_cons)

      lemma TI_Parallel_list: "(\<forall> A \<in> set As . io_diagram A) \<Longrightarrow> TI (Trs (Parallel_list As)) = TVs (op_list [] op \<oplus> (map In As))"
        apply (induction As)
        apply simp
        apply (simp add: ParallelId_def)
        apply (simp add: Parallel_def)
        apply (subst TI_comp)
        apply simp_all
        apply (simp_all add: In_Parallel)
        by (simp add: io_diagram_def)

      lemma TO_Parallel_list: "(\<forall> A \<in> set As . io_diagram A) \<Longrightarrow> TO (Trs (Parallel_list As)) = TVs (concat (map Out As))"
        apply (induction As, simp_all)
        apply (simp add: Parallel_def)
        apply (subst TO_comp)
        apply simp_all
        apply (simp_all add: In_Parallel TI_Parallel_list)
        by (simp_all add: io_diagram_def)

      lemma fbtype_aux: "(Type_OK As) \<Longrightarrow> loop_free As \<Longrightarrow> VarFB (Parallel_list As) = a # L \<Longrightarrow>
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
  
      lemma TI_parallel_list: "(\<forall> A \<in> set As . io_diagram A) \<Longrightarrow> TI (parallel_list (map Trs As)) = TVs (concat (map In As))"
        apply (induction As)
        by (simp_all add: parallel_list_def io_diagram_def)
  
      lemma TO_parallel_list: "(\<forall> A \<in> set As . io_diagram A) \<Longrightarrow>TO (parallel_list (map Trs As)) = TVs (concat (map Out As))"
        apply (induction As)
        by (simp_all add: parallel_list_def io_diagram_def)


      lemma Trs_Parallel_list_aux_a: "Type_OK As \<Longrightarrow> io_diagram a \<Longrightarrow>
            [In a \<oplus> In (Parallel_list As) \<leadsto> In a @ In (Parallel_list As)] oo Trs a \<parallel> ([In (Parallel_list As) \<leadsto> concat (map In As)] oo parallel_list (map Trs As)) =
            [In a \<oplus> In (Parallel_list As) \<leadsto> In a @ In (Parallel_list As)] oo ([In a \<leadsto> In a ] \<parallel> [In (Parallel_list As) \<leadsto> concat (map In As)] oo Trs a \<parallel> parallel_list (map Trs As))"
        apply (subst comp_parallel_distrib)
        apply (simp add:   io_diagram_def)
        apply (simp )
        apply (subst TI_parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (subst comp_id_switch) 
        by (simp_all add: io_diagram_def)
  
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
        apply (simp add: io_diagram_def)
        apply (subst TI_parallel_list)
        apply (simp add: Type_OK_def)
        apply simp
        apply (subst Trs_Parallel_list_aux_b)
        apply (simp add: io_diagram_def)
        using io_diagram_def io_diagram_parallel_list apply blast
        apply (subst In_Parallel)
        by auto
(*
CompA update
      lemma CompA_Id[simp]: "CompA A \<box> = \<box>"
        by (simp add: CompA_def comp_def ParallelId_def)
*) 
          
lemma CompA_Id[simp]: "A \<rhd> \<box> = \<box>"
  by (simp add: CompA_def comp_def ParallelId_def)
    

lemma io_diagram_ParallelId[simp]: "io_diagram \<box>"
  by (simp add: io_diagram_def ParallelId_def)

(*move*)
lemma in_equiv_aux_a :"distinct x \<Longrightarrow> distinct y \<Longrightarrow>  set z \<subseteq> set x \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> z] \<parallel> [y \<leadsto> y] = [x \<oplus> y \<leadsto> z @ y]"
  by (subst switch_par_comp_Subst, simp_all add: distinct_addvars set_addvars Subst_eq)

(*move*)
lemma in_equiv_Parallel_aux_d: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set u \<subseteq> set x \<Longrightarrow> perm y v
           \<Longrightarrow> [x \<oplus> y \<leadsto> x @ v] oo [x \<leadsto> u] \<parallel> [v \<leadsto> v] = [x \<oplus> y \<leadsto> u @ v]"
        proof -
          assume [simp]: "distinct x"
          assume [simp]: "distinct y"
          assume [simp]: "set u \<subseteq> set x"
          assume [simp]: "perm y v"

          define v' where "v' \<equiv> newvars x (TVs v)"

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

(*move*)
lemma comp_par_switch_subst: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set u \<subseteq> set x \<Longrightarrow> set v \<subseteq> set y 
      \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> u] \<parallel> [y \<leadsto> v] = [x \<oplus> y \<leadsto> u @ v]"
        proof -
          assume [simp]: "distinct x"
          assume [simp]: "distinct y"
          assume [simp]: "set u \<subseteq> set x"
          assume [simp]: "set v \<subseteq> set y"
        
          define x' where "x' \<equiv> newvars (x@y) (TVs x)"

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
          
(*move*)
      lemma in_equiv_Parallel_aux_b :"distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm u x \<Longrightarrow> perm y v \<Longrightarrow> [x \<oplus> y \<leadsto> x @ y] oo [x \<leadsto> u] \<parallel> [y \<leadsto> v] = [x \<oplus> y \<leadsto> u @ v]"
        by (subst comp_par_switch_subst, simp_all )

(*move*)
lemma [simp]: "set x \<subseteq> set (x \<oplus> y)"
  by (simp add: set_addvars)
    
(*move*)
lemma [simp]: "set y \<subseteq> set (x \<oplus> y)"
  by (simp add: set_addvars)

      declare distinct_addvars [simp]

lemma in_equiv_Parallel: "io_diagram B \<Longrightarrow> io_diagram B' \<Longrightarrow> in_equiv A B \<Longrightarrow> in_equiv A' B' \<Longrightarrow> in_equiv (A ||| A') (B ||| B')"
  apply (frule in_equiv_io_diagram, simp_all)
  apply (frule_tac A = A' in in_equiv_io_diagram, simp)
  apply (frule_tac A = A in in_equiv_io_diagram, simp)
  apply (simp add: in_equiv_def io_diagram_def, safe)
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

(*
lemma CompA_in[simp]: "length (Out A) = 1 \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> A \<rhd> B = A ;; B"
  by (simp add: CompA_def)

lemma CompA_not_in[simp]: "length (Out A) = 1 \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> CompA A B = B"
  by (simp add: CompA_def out_def)
*)

lemma CompA_in[simp]: "out A \<in> set (In B) \<Longrightarrow> A \<rhd> B = A ;; B"
  by (simp add: CompA_def)

lemma CompA_not_in[simp]: "out A \<notin> set (In B) \<Longrightarrow> A \<rhd> B = B"
  by (simp add: CompA_def out_def)

          
lemma in_equiv_CompA_Parallel_a: " deterministic (Trs A) \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C 
  \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> out A \<in> set (In C) 
  \<Longrightarrow> in_equiv ((A \<rhd> B) ||| (A \<rhd> C)) (A \<rhd> (B ||| C))"
        apply (simp add: in_equiv_def, safe)
        apply (simp add: In_CompA set_addvars)
        apply (simp_all add: Comp_def CompA_def Parallel_def Let_def Var_def set_addvars diff_inter_right diff_inter_left)
        apply (simp_all add: Out_out par_empty_left)
        apply (simp add: addvars_assoc [THEN sym])
        apply (metis addvars_assoc addvars_minus perm_mset)
        apply (simp_all add: set_addvars)
        proof -
          assume [simp]: "deterministic (Trs A)"
          assume [simp]: "length (Out A) = Suc 0"
          assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"
          assume [simp]: "io_diagram C"
          assume [simp]: "out A \<in> set (In B)"
          assume [simp]: "out A \<in> set (In C)"

          define IA where "IA \<equiv> In A"
          define IB where "IB \<equiv> In B"
          define IC  where "IC \<equiv> In C"
          define OA where "OA \<equiv> Out A"
          define IBA where "IBA \<equiv> IB \<ominus> OA"
          define ICA where "ICA \<equiv> IC \<ominus> OA"

          define IBA' where "IBA' \<equiv> newvars (IA @ OA @ ICA @ IBA) (TVs IBA)"
          define IA' where "IA' \<equiv> newvars (IBA' @ IA @ ICA) (TVs IA)"
          define ICA' where "ICA' \<equiv> newvars (IA' @ IBA' @ IA @ OA) (TVs ICA)"
          define OA' where "OA' \<equiv> newvars (OA @ IBA' @ ICA' @ IBA @ ICA @ IA) (TVs OA)"

          have [simp]: "TVs IA = TI (Trs A)"
            using \<open>io_diagram A\<close> io_diagram_def IA_def by fastforce

          have [simp]: "distinct IA"
            using \<open>io_diagram A\<close> io_diagram_def IA_def by fastforce

          have [simp]: "TVs OA = TO (Trs A)"
            using \<open>io_diagram A\<close> io_diagram_def OA_def by fastforce

          have [simp]: "distinct OA "
            using \<open>io_diagram A\<close> io_diagram_def OA_def by fastforce
            
          have [simp]: "TVs IB = TI (Trs B)"
            using \<open>io_diagram B\<close> io_diagram_def IB_def by fastforce

          have [simp]: "distinct IB"
            using \<open>io_diagram B\<close> io_diagram_def IB_def by fastforce

          have [simp]: "TVs IC = TI (Trs C)"
            using \<open>io_diagram C\<close> io_diagram_def IC_def by fastforce

          have [simp]: "distinct IC"
            using \<open>io_diagram C\<close> io_diagram_def IC_def by fastforce

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

      lemma in_equiv_CompA_Parallel_c: "length (Out A) = 1 \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> out A \<in> set (In C) \<Longrightarrow> 
              in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        apply (simp add: in_equiv_def, safe)
        apply (simp add: Comp_def Let_def In_CompA set_addvars Var_def diff_inter_left diff_inter_right)
        apply (simp add: addvars_minus diff_disjoint Out_out)
        apply (subst set_perm)
        apply (simp add:  io_diagram_def )
        apply (simp add:  io_diagram_def )
        apply (simp add: set_addvars set_diff)
        apply blast
        apply simp
        apply (simp_all add: Comp_def Let_def BBB_a Var_def)
        apply (simp_all add: Out_out)
        apply (simp add: Let_def Parallel_def In_CompA Var_def Comp_def par_empty_left set_addvars diff_inter_left diff_inter_right Out_out[THEN sym] diff_union)
        apply (simp add: Out_out set_addvars par_empty_left)
        apply (simp add: Out_out[THEN sym])
        proof -
          assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"
          assume [simp]: "io_diagram C"
          assume [simp]: "length (Out A) = Suc 0"
          assume [simp]: "out A \<notin> set (In B)"
          assume [simp]: "out A \<in> set (In C)"

          define IA where "IA \<equiv> In A"
          define IB where "IB \<equiv> In B"
          define IC where "IC \<equiv> In C"
          define OA where "OA \<equiv> Out A"

          define ICA where "ICA \<equiv> IC \<ominus> OA"

          define IB' where "IB' \<equiv> newvars (IA @ OA @ ICA) (TVs IB)"

          define ICA' where "ICA' \<equiv> newvars (IA @ IB' @ OA @ ICA) (TVs ICA)"

          have [simp]: "TVs IB = TI (Trs B)"
            using IB_def \<open>io_diagram B\<close> io_diagram_def by blast

          have [simp]: "TVs IA = TI (Trs A)"
            using IA_def \<open>io_diagram A\<close> io_diagram_def by blast

          have [simp]: "TVs OA = TO (Trs A)"
            using OA_def \<open>io_diagram A\<close> io_diagram_def by blast

          have [simp]: "TVs IC = TI (Trs C)"
            using IC_def \<open>io_diagram C\<close> io_diagram_def by blast

          have [simp]: "distinct IB"
            using IB_def \<open>io_diagram B\<close> io_diagram_def by blast

          have [simp]: "distinct IB'"
            by (simp add: IB'_def)

          have [simp]: "distinct IA"
            using IA_def \<open>io_diagram A\<close> io_diagram_def by blast

          have [simp]: "distinct IC"
            using IC_def \<open>io_diagram C\<close> io_diagram_def by blast

          have [simp]: "set IB' \<inter> set IA = {}"
            by (metis IB'_def UnCI disjoint_iff_not_equal newvars_old_distinct set_append)

          have [simp]: "distinct OA"
            using OA_def \<open>io_diagram A\<close> io_diagram_def by blast

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
                  apply (metis append_assoc perm_append2 perm_append_swap)
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
            apply (metis mset_inter_diff perm_mset union_code)
             apply (simp add: inter_diff_distrib diff_emptyset)
              by (metis append_assoc perm_append2 perm_append_swap)
            

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

          define IA' where "IA' \<equiv> newvars (IB \<oplus> ICA) (TVs IA)"

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



      lemmas distinct_addvars distinct_diff

lemma io_diagram_distinct: assumes A: "io_diagram A" shows [simp]: "distinct (In A)" 
  and [simp]: "distinct (Out A)" and [simp]: "TI (Trs A) = TVs (In A)" 
  and [simp]: "TO (Trs A) = TVs (Out A)"
  using A by (simp_all add: io_diagram_def)
    


      declare Subst_not_in_a  [simp]
      declare Subst_not_in  [simp]

      (*move*)
      lemma [simp]: "set x' \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> TVs x' = TVs y' \<Longrightarrow> Subst (x @ x') (y @ y') z = Subst x y z"
        by (metis Subst_not_in length_TVs)

      lemma [simp]: "set x \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> TVs x' = TVs y' \<Longrightarrow> Subst (x @ x') (y @ y') z = Subst x' y' z"
        by (metis Subst_not_in_a length_TVs)

      lemma [simp]: "set x \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> Subst x y z = z"
        by (metis Subst_inex length_TVs)

      lemma [simp]: "distinct x \<Longrightarrow> TVs x = TVs y \<Longrightarrow> Subst x y x = y"
        by (metis Subst_all length_TVs)

      lemma "TVs x = TVs y \<Longrightarrow> length x = length y"
        by (metis length_TVs)

        thm length_TVs

(*end simplification rules*)

      lemma in_equiv_switch_Parallel: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (Out A) \<inter> set (Out B) = {}  \<Longrightarrow> 
        in_equiv (A ||| B) ((B ||| A) ;; [[ Out B @ Out A \<leadsto> Out A @ Out B]])"
        apply (simp add: in_equiv_def Let_def Parallel_def Comp_def VarSwitch_def Var_def diff_inter_left diff_inter_right diff_eq par_empty_left par_empty_right)
        apply safe
        apply (metis addvars_def perm_switch perm_tp perm_trans io_diagram_def)
        proof -
          assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"

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

lemma in_out_equiv_Parallel: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (Out A) \<inter> set (Out B) = {}  \<Longrightarrow>  in_out_equiv (A ||| B) (B ||| A)"
    apply (frule in_equiv_switch_Parallel, simp_all)
    apply (simp add: in_equiv_def in_out_equiv_def Parallel_def VarSwitch_def Let_def Comp_def Var_def par_empty_left par_empty_right, safe)
    using distinct_perm_switch io_diagram_distinct(1) apply blast
    using perm_tp apply blast
    apply (unfold io_diagram_def)
    apply (simp add: comp_assoc)
    by (subst switch_comp, auto)


      declare Subst_eq [simp]

lemma assumes "in_equiv A A'" shows [simp]: "perm (In A) (In A')" 
  using assms in_equiv_def by blast
    

lemma Subst_cancel_left_type: "set x \<inter> set z = {} \<Longrightarrow> TVs x = TVs y \<Longrightarrow> Subst (x @ z) (y @ z) w = Subst x y w"
  by (metis Subst_cancel_left length_TVs)
    

lemma diff_eq_set_right: "set y = set z \<Longrightarrow> (x \<ominus> y) = (x \<ominus> z)"
  by (induction x, simp_all)

      lemma [simp]: "set (y \<ominus> x) \<inter> set x = {}"
        by (auto simp add: set_diff)

lemma in_equiv_Comp: "io_diagram A' \<Longrightarrow> io_diagram B' \<Longrightarrow> in_equiv A A' \<Longrightarrow> in_equiv B B' \<Longrightarrow> in_equiv (A ;; B) (A' ;; B')"
        proof -
          assume [simp]: "io_diagram A'"
          assume [simp]: "io_diagram B'"
          assume [simp]: "in_equiv A A'"
          assume [simp]: "in_equiv B B'"

          have [simp]: "io_diagram A"
            using \<open>in_equiv A A'\<close> \<open>io_diagram A'\<close> in_equiv_io_diagram by blast
          have [simp]: "io_diagram B"
            using \<open>in_equiv B B'\<close> \<open>io_diagram B'\<close> in_equiv_io_diagram by blast

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

          define v where "v \<equiv> newvars (In A @ In B) (TVs (Out A'))"

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


      lemma "io_diagram A' \<Longrightarrow> io_diagram B' \<Longrightarrow> in_equiv A A' \<Longrightarrow> in_equiv B B' \<Longrightarrow> in_equiv (CompA A  B) (CompA A' B')"
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
        define z' where "z' \<equiv> newvars y' (TVs z)"

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
        define z' where "z' \<equiv> newvars y' (TVs z)"

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


lemma CCC_a: "distinct x \<Longrightarrow> distinct y \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set u \<subseteq> set y \<Longrightarrow> TVs z = ts 
    \<Longrightarrow> [x \<leadsto> y @ z] oo [y \<leadsto> u] \<parallel> (ID ts) = [x \<leadsto> u @ z]"
  by (subst CCC_d, simp_all)
    
        

lemma CCC_b: "distinct x \<Longrightarrow> distinct z \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set z \<subseteq> set x \<Longrightarrow> set u \<subseteq> set z 
    \<Longrightarrow> TVs y = ts \<Longrightarrow> [x \<leadsto> y @ z] oo  (ID ts) \<parallel> [z \<leadsto> u] = [x \<leadsto> y @ u]"
  by (subst CCC_e, simp_all)
    


      thm par_switch_eq_dist

      lemma in_equiv_CompA_Parallel_b: "length (Out A) = 1 \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> out A \<in> set (In B) 
        \<Longrightarrow>  out A \<notin> set (In C) \<Longrightarrow> in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        proof simp
          assume [simp]: "length (Out A) = Suc 0"
          assume [simp]: "out A \<notin> set (In C)"
          assume [simp]: "out A \<in> set (In B)"

          assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"
          assume [simp]: "io_diagram C"
        
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

         define v where "v \<equiv> newvars (In A @ In B @ In C) (TVs (Out A))"

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
          apply (simp add: par_assoc)
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

      lemma in_equiv_CompA_Parallel_d: "length (Out A) = 1 \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> out A \<notin> set (In C) \<Longrightarrow> 
              in_equiv (CompA A B ||| CompA A C) (CompA A (B ||| C))"
        by (simp add: in_equiv_def In_CompA set_addvars BBB_a Parallel_def )

lemma in_equiv_CompA_Parallel: " deterministic (Trs A) \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow>
          in_equiv ((A \<rhd> B) ||| (A \<rhd> C)) (A \<rhd> (B ||| C))"
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
 

lemma fb_less_step_compA: "deterministic (Trs A) \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> io_diagram A \<Longrightarrow> Type_OK As 
  \<Longrightarrow> in_equiv (Parallel_list (fb_less_step A As)) (CompA A (Parallel_list As))"
        apply (induction As)
        apply (simp_all add: fb_less_step_def in_equiv_eq)
        apply (rule_tac B = "(CompA A a ||| CompA A (Parallel_list As))" in in_equiv_tran)
        apply (rule io_diagram_CompA, simp_all)
        apply (rule io_diagram_Parallel)
        apply (simp add: Type_OK_simp)
        apply (rule io_diagram_parallel_list)
        apply (simp add: Type_OK_simp, safe)
        apply (simp add: Out_Parallel BBB_a Type_OK_out)
        apply (simp add: Type_OK_simp image_def)
        apply (rule in_equiv_Parallel)
        apply (rule io_diagram_CompA, simp_all)
        apply (simp add: Type_OK_simp)
        apply (rule io_diagram_CompA, simp_all)
        apply (rule io_diagram_parallel_list, simp)
        apply (rule in_equiv_eq)
        apply (rule io_diagram_CompA, simp_all)
        apply (simp add: Type_OK_simp)
        apply (rule in_equiv_CompA_Parallel, simp_all)
        apply (simp add: Type_OK_simp)
        by (rule io_diagram_parallel_list, simp)
      

(*simp rules*)

          (*move*)
lemma switch_eq_Subst: "distinct x \<Longrightarrow> distinct u \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> set v \<subseteq> set u \<Longrightarrow> TVs x = TVs u 
    \<Longrightarrow> Subst x u y = v \<Longrightarrow> [x \<leadsto> y] = [u \<leadsto> v]"
  using Subst_switch_a by blast

(*move*)
lemma [simp]: "set y \<subseteq> set y1 \<Longrightarrow> distinct x1 \<Longrightarrow> TVs x1 = TVs y1 \<Longrightarrow> Subst x1 y1 (Subst y1 x1 y) = y"
  by (metis Subst_Subst_inv length_TVs)
    
(*move*)
lemma [simp]: "set z \<subseteq> set x \<Longrightarrow> TVs x  = TVs y \<Longrightarrow> set (Subst x y z) \<subseteq> set y"
  by (metis Subst_set_incl length_TVs)
    

      thm distinct_Subst

(*move*)
      lemma distinct_Subst_aa: "\<And> y . 
            distinct y \<Longrightarrow> length x = length y \<Longrightarrow> a \<notin> set y \<Longrightarrow> set z \<inter> (set y - set x) = {} \<Longrightarrow> a \<noteq> aa 
      \<Longrightarrow> a \<notin> set z \<Longrightarrow> aa \<notin> set z \<Longrightarrow> distinct z  \<Longrightarrow> aa \<in> set x 
      \<Longrightarrow> subst x y a \<noteq> subst x y aa"
        apply (induction x, simp_all)
        apply (case_tac y, simp_all, safe)
        apply (metis subst_in_set subst_notin)
        apply (simp add: subst_in_set)
        apply (metis subst_subst_inv subst_notin) 
        by (metis subst_subst_inv subst_notin)

lemma distinct_Subst_ba: "distinct y \<Longrightarrow> length x = length y \<Longrightarrow> set z \<inter> (set y - set x) = {}  
    \<Longrightarrow> a \<notin> set z \<Longrightarrow> distinct z  \<Longrightarrow> a \<notin> set y \<Longrightarrow> subst x y a \<notin> set (Subst x y z)"
        apply (induction z, simp_all, safe)
        apply (simp add: distinct_Subst_a)
        by (simp add: distinct_Subst_aa)

lemma distinct_Subst_ca: "distinct y \<Longrightarrow> length x = length y \<Longrightarrow> set z \<inter> (set y - set x) = {} 
    \<Longrightarrow> a \<notin> set z \<Longrightarrow> distinct z \<Longrightarrow> a \<in> set x \<Longrightarrow> subst x y a \<notin> set (Subst x y z)"
        apply (induction z, simp_all, safe)
        apply (metis distinct_Subst_aa)
        by (metis subst_subst_inv)

lemma [simp]: "set z \<inter> (set y - set x) = {} \<Longrightarrow>  distinct y \<Longrightarrow> distinct z \<Longrightarrow> length x = length y 
  \<Longrightarrow> distinct (Subst x y z)"
        apply (induction z, simp_all, safe)
        apply (simp add: distinct_Subst_ba)
        by (simp add: distinct_Subst_ca)

(*end simp rules*)



lemma deterministic_Comp: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> deterministic (Trs A) \<Longrightarrow> deterministic (Trs B) 
  \<Longrightarrow> deterministic (Trs (A ;; B))"
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

lemma deterministic_CompA: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> deterministic (Trs A) \<Longrightarrow> deterministic (Trs B) 
  \<Longrightarrow> deterministic (Trs (A \<rhd> B))"
        by (simp add: CompA_def deterministic_Comp)


      lemma parallel_list_empty[simp]: "parallel_list [] = ID []"
        by (simp add: parallel_list_def)

      lemma parallel_list_append: "parallel_list (As @ Bs) = parallel_list As \<parallel> parallel_list Bs"
        apply (induction As)
        apply (simp_all)
        by (simp add: parallel_list_cons par_assoc)

          (*move*)
lemma par_swap_aux: "distinct p \<Longrightarrow> distinct (v @ u @ w) \<Longrightarrow> 

          TI A = TVs x \<Longrightarrow> TI B = TVs y \<Longrightarrow> TI C = TVs z \<Longrightarrow>
          TO A = TVs u \<Longrightarrow> TO B = TVs v \<Longrightarrow> TO C = TVs w \<Longrightarrow>
          set x \<subseteq> set p \<Longrightarrow> set y \<subseteq> set p \<Longrightarrow> set z \<subseteq> set p \<Longrightarrow> set q \<subseteq> set (u @ v @ w) \<Longrightarrow>
          [p \<leadsto> x @ y @ z] oo (A \<parallel> B \<parallel> C) oo [u @ v @ w \<leadsto> q] = [p \<leadsto> y @ x @ z] oo (B \<parallel> A \<parallel> C) oo [v @ u @ w \<leadsto> q]"
        proof -
          define x' where "x' \<equiv> newvars [] (TI A)"
          define y' where "y' \<equiv> newvars x' (TI B)"
          define z' where "z' \<equiv> newvars (x' @ y') (TI C)"
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
              apply (metis append.assoc perm_tp perm_union_left)
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
            using InAs \<open>Type_OK As\<close> io_diagram_def io_diagram_parallel_list by blast

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
            using \<open>Type_OK (Cs @ Ds)\<close> io_diagram_def io_diagram_parallel_list by blast


          define C where "C \<equiv> parallel_list (map Trs Cs)"
          define D where "D \<equiv> parallel_list (map Trs Ds)"
          define InCs where "InCs \<equiv> concat (map In Cs)"
          define InDs where "InDs \<equiv> concat (map In Ds)"
          define OutCs where "OutCs \<equiv> Out (Parallel_list Cs)"
          define OutDs where "OutDs \<equiv> Out (Parallel_list Ds)"

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
            by (metis OutAs_simp Out_Parallel \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> append.simps(2) disjoint_iff_not_equal distinct_append list.set_intros(1) io_diagram_def io_diagram_parallel_list)
  
          have [simp]: " distinct OutDs "
            by (metis Type_OK_def OutAs_simp \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> distinct_append)

          have [simp]: " a \<notin> set OutCs "
            by (metis OutAs_simp Out_Parallel \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> append.simps(2) disjoint_iff_not_equal distinct_append list.set_intros(1) io_diagram_def io_diagram_parallel_list)

          have [simp]: "set OutCs \<inter> set OutDs = {}"
            by (metis Type_OK_def OutAs_simp \<open>OutAs = OutCs @ [a] @ OutDs\<close> \<open>Type_OK As\<close> append_assoc dist_perm distinct_append perm_tp)

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

          from \<open>Type_OK As\<close> have [simp]: "io_diagram A"
            by (unfold Type_OK_def, simp)

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

            

          define E where "E \<equiv> C \<parallel> D"
          define InE where "InE \<equiv> InCs @ InDs"
          define OutE where "OutE \<equiv> OutCs @ OutDs"

          from B have C: "?Ta = [a # y \<leadsto> In A @ InE] oo (Trs A \<parallel> E) oo [ [a ] @ OutE \<leadsto> a # z]"
            by (unfold E_def InE_def OutE_def par_assoc, simp)

          define y' where "y' \<equiv> newvars (a#y) (TVs y)"

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
            using Subst_cons_aux_a \<open>TVs y' = TVs y\<close> \<open>distinct y'\<close> \<open>distinct y\<close> \<open>set y \<inter> set y' = {}\<close> TVs_length_eq by blast

          have [simp]: "Subst (a # y @ y') (a # y @ y) (y @ a # y') = y @ a # y"
            by (simp add: Subst_append)

          have Au: "set InAs = set InCs \<union> (set (In A) \<union> set InDs)"
            by (simp add: InAs In_Parallel A InCs_def InDs_def, auto)

          have Av: "set InAs = insert a (set y)"
            using ListProp.perm_set_eq permInAs by fastforce

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


          define w where "w \<equiv> InAs' \<ominus> [a]"
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
        by (simp add: perm_mset)

(*used in fb_Parallel_list_fb_out_less_step - Feedbackless.thy*)
lemma fb_CompA: "Type_OK As \<Longrightarrow> A \<in> set As \<Longrightarrow> out A = a \<Longrightarrow> a \<notin> set (In A) \<Longrightarrow> C = A \<rhd> (Parallel_list (As \<ominus> [A])) \<Longrightarrow>
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



          define InAs' where "InAs' \<equiv> In (Parallel_list (As \<ominus> [A]))"

          have Ax: "io_diagram A"
            using \<open>Type_OK As\<close> \<open>A \<in> set As\<close> by (unfold Type_OK_def, simp)
            
          from Ax have [simp]: "TI (Trs A) = TVs (In A)"
            by simp

          from Ax have [simp]: "TO (Trs A) = [TV a]"
            by (simp add:  Out_out)

          have "Type_OK (As \<ominus> [A])"
            using \<open>Type_OK As\<close> by (unfold Type_OK_simp, simp add: set_diff BBB_c)

          from this have Ay: "io_diagram (Parallel_list (As \<ominus> [A]))"
            using io_diagram_parallel_list by blast
            

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

          have io_diagram_C: "io_diagram C"
            apply (simp add: C)
            apply (subst io_diagram_Comp, simp_all)
            using Ax Ay apply simp_all
            by (simp add: Out_out Out_Parallel set_diff)

          have [simp]: "perm (a # z) (Out (Parallel_list As))"
            using Av apply (rule_tac y = "a # Out C" in perm_trans, simp_all)
            apply (subst set_perm, simp_all, safe)
            apply (simp add: C Comp_def Let_def Out_Parallel set_diff)
            using \<open>Type_OK As\<close> apply (simp add: A Type_OK_simp Out_out)
            apply auto [1]
            using \<open>io_diagram C\<close> io_diagram_def apply blast
            using Type_OK_def  Out_Parallel apply fastforce
            apply (simp_all add: Out_Parallel A Out_out union_diff AAA_c)
            apply (simp_all add: C Comp_def Let_def Out_Parallel set_diff Out_out)
            apply auto [1]
            apply (simp_all add: A)
            apply auto
            apply (metis Un_Diff Un_insert_left \<open>(Cs \<ominus> [A]) = Cs\<close> \<open>(Ds \<ominus> [A]) = Ds\<close> insert_Diff insert_iff list.set(1) list.simps(15) set_diff)
            by (metis Un_Diff Un_iff \<open>(Ds \<ominus> [A]) = Ds\<close> empty_set list.simps(15) set_diff)
            

          from io_diagram_C have dist_C: "distinct (In C)"
            by (simp)
            
          from dist_C and Au have [simp]: "distinct y"
            using dist_perm perm_sym by blast

          have [simp]: "perm y (In A \<oplus> (InAs' \<ominus> [a]))"
            using Au by (simp add: InAs'_def C Comp_def Let_def)

          have Ay: "io_diagram (Parallel_list As)"
            using \<open>Type_OK As\<close> io_diagram_parallel_list by blast

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
    

      lemma in_equiv_fb_fb_less_step_TO_CHECK: "loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow>
        VarFB (Parallel_list As) = a # L \<Longrightarrow> Bs = fb_out_less_step a As 
        \<Longrightarrow>  in_equiv (FB (Parallel_list As)) (FB (Parallel_list Bs))"
        apply (frule VarFB_fb_out_less_step, simp_all)
        apply (simp add: in_equiv_def)
        apply (simp add: FB_def Let_def VarFB_def)
        apply (simp add: funpow_swap1)
        apply (cut_tac S = "([L @ (In (Parallel_list (fb_out_less_step a As)) \<ominus> L) \<leadsto> In (Parallel_list (fb_out_less_step a As))] oo
                  Trs (Parallel_list (fb_out_less_step a As)) oo
                  [Out (Parallel_list (fb_out_less_step a As)) \<leadsto> L @ (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L)])"
              and A = "[In (Parallel_list As) \<ominus> a # L \<leadsto> In (Parallel_list (fb_out_less_step a As)) \<ominus> L]"
              and tsa = "TVs L"
              and ts = "TVs (Out (Parallel_list (fb_out_less_step a As)) \<ominus> L)"
            in fb_indep_left_a)
        apply (rule fbtype_aux, simp_all)
        apply (simp add: VarFB_def)
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

          have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> io_diagram A"
            apply (subgoal_tac "Type_OK As")
            apply (simp add: Type_OK_def)
            by simp

          have [simp]: "\<And> A . A \<in> set (fb_out_less_step a As) \<Longrightarrow> io_diagram A"
            by (metis Type_OK_def VarFB_def Type_OK_fb_out_less_step \<open>Type_OK As\<close> \<open>loop_free As\<close> aux)
           

          define InAs where "InAs \<equiv> In (Parallel_list As)"
          define InStAs where "InStAs \<equiv> In (Parallel_list (fb_out_less_step a As))"

          define OutAs where "OutAs \<equiv> Out (Parallel_list As)"
          define OutStAs where "OutStAs \<equiv> Out (Parallel_list (fb_out_less_step a As))"

          have [simp]: "distinct InAs"
            using InAs_def \<open>Type_OK As\<close> io_diagram_def io_diagram_parallel_list by blast

          have [simp]: " distinct (InAs \<ominus> a # L)"
            apply (subst distinct_diff)
            apply (simp add: InAs_def)
            using \<open>Type_OK As\<close> io_diagram_def io_diagram_parallel_list apply blast
            by simp

          have [simp]: "set L \<inter> set (InAs \<ominus> a # L) = {}"
            apply (simp add: set_diff)
            by blast

          have PermInAs[simp]: "perm (a # L @ (InAs \<ominus> a # L)) InAs"
            by (metis Var_def Cons_eq_appendI InAs_def \<open>Type_OK As\<close> aux diff_inter_right perm_switch_aux_f io_diagram_def io_diagram_parallel_list)


          obtain A where AAa[simp]: "A \<in> set As" and AAb: "a = out A"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "VarFB (Parallel_list As) = a # L")
            apply (frule VarFB_cons_out, auto)
            by (simp add: VarFB_def)

          obtain B where AAc: "B \<in> set As" and AAd: "a \<in> set (In B)"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "VarFB (Parallel_list As) = a # L")
            apply (frule VarFB_cons_out_In)
            apply auto
            by (simp add: VarFB_def)
         
          have [simp]: "B \<noteq> A"
            using AAa AAb AAd BBBB_f \<open>Type_OK As\<close> \<open>loop_free As\<close> by blast

          have [simp]: "length (Out A) = 1"
            using AAa Type_OK_simp \<open>Type_OK As\<close> by blast

          have [simp]:"out A \<in> set (In B)"
            using AAb AAd by auto

          have [simp]: "distinct InStAs"
            apply (simp add: InStAs_def)
            apply (subgoal_tac "io_diagram (Parallel_list (fb_out_less_step a As))")
            using io_diagram_def apply blast
            by (simp add: AAb Type_OK_fb_out_less_step_aux fb_out_less_step_def mem_get_comp_out mem_get_other_out io_diagram_parallel_list)

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
            by (metis VarFB_def VarFB_fb_out_less_step \<open>Type_OK As\<close> \<open>loop_free As\<close> aux)

          have [simp]: "perm (InAs \<ominus> a # L) (InStAs \<ominus> L)"
            apply (simp add: InAs_def InStAs_def)
            apply (cut_tac As = As and a  = a and L = L in perm_FB_Parallel, simp_all)
            apply (simp add: VarFB_def)
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

          define C where "C \<equiv> CompA A (Parallel_list (As \<ominus> [A]))"


          have [simp]: "Type_OK (As \<ominus> [A])"
            using \<open>Type_OK As\<close> 
            by (metis AAa Type_OK_def concat_map_Out_get_other_out distinct_diff inter_subset mem_get_other_out notin_inter)

          have "io_diagram C"
            apply (simp add: C_def)
            apply (rule io_diagram_CompA)
            using \<open>Type_OK As\<close>
            apply simp_all
            apply (rule io_diagram_parallel_list)
            by simp

          have [simp]: "out A \<in> set (In (Parallel_list (As \<ominus> [A])))"
            apply (simp add: In_Parallel set_diff)
            using AAc \<open>B \<noteq> A\<close> \<open>out A \<in> set (In B)\<close> by blast

          have [simp]: "perm (L @ (InAs \<ominus> out A # L)) (In C)"
            apply (rule set_perm, simp_all)
            using AAb \<open>distinct (InAs \<ominus> a # L)\<close> \<open>distinct L\<close> \<open>set L \<inter> set (InAs \<ominus> a # L) = {}\<close> distinct_append apply blast
            using \<open>io_diagram C\<close> apply (simp)
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
            using OutAs_def \<open>Type_OK As\<close> distinct_diff io_diagram_def io_diagram_parallel_list apply blast
            apply (simp add: set_diff)
            using \<open>io_diagram C\<close> io_diagram_def apply auto[1]
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

          define D where "D \<equiv> Parallel_list (fb_less_step A (As \<ominus> [A]))"

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
            by (metis AAa AAb C_def Type_OK_def Type_OK_fb_out_less_step_aux Ua \<open>Type_OK As\<close> inter_subset map_Out_fb_out_less_step mem_get_other_out notin_inter io_diagram_CompA io_diagram_def io_diagram_parallel_list)
            

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
            by (metis VarFB_def Type_OK_fb_out_less_step \<open>Type_OK As\<close> \<open>Var (Parallel_list As) (Parallel_list As) = a # L\<close> \<open>loop_free As\<close>)

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
      

      lemma io_diagram_FB_Parallel_list: "Type_OK As \<Longrightarrow> io_diagram (FB (Parallel_list As))"
        by (simp_all add:  Type_ok_FB io_diagram_parallel_list)


      lemma [simp]: "io_diagram A \<Longrightarrow> \<lparr>In = In A, Out = Out A, Trs =  Trs A\<rparr> = A"
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

          from this have "(IO_Rel (map (CompA A) (As \<ominus> [A])))\<^sup>+ \<subseteq> (IO_Rel As)\<^sup>+"
            apply (rule trancl_Int_subset, safe)
            apply (rule_tac y = y in  trancl_trans )
            apply blast
            by blast

          from this and C and D show "False"
            by (simp add: loop_free_def, auto)
       qed

      
      theorem in_equiv_FB_fb_less_delete: "\<And> As . Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = L \<Longrightarrow>  
                  in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As)) \<and> io_diagram (Parallel_list (fb_less L As))"
        apply (induction L)
        apply (frule io_diagram_parallel_list)
        apply (simp add: FB_def VarFB_def diff_emptyset)
        apply (rule in_equiv_eq, simp, simp)
        proof -
          fix a:: 'var
          fix L :: "'var list"
          fix As:: "('var, 'a) Dgr list"
          assume A: "(\<And>As ::('var, 'a) Dgr list. Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = L \<Longrightarrow> in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As)) \<and> io_diagram (Parallel_list (fb_less L As)))"
          assume [simp]: "loop_free As"
          assume [simp]: "Type_OK As"
          assume [simp]: "VarFB (Parallel_list As) = a # L"
          assume [simp]: "Deterministic As"
  
          define Bs where "Bs \<equiv> fb_out_less_step a As"
  
          from this have Bs_simp: "Bs = fb_out_less_step a As"
            by simp

          obtain A where AAa[simp]: "A \<in> set As" and AAb: "a = out A"
            apply (subgoal_tac "Type_OK As")
            apply (subgoal_tac "VarFB (Parallel_list As) = a # L")
            by (frule VarFB_cons_out, auto)
  
          from AAb have [simp]: "Deterministic Bs"
            apply (simp only: Bs_simp)
            by (rule_tac A = A in  Deterministic_fb_out_less_step, simp_all)
  
          have [simp]: "loop_free Bs"
            apply (simp only: Bs_simp)
            by (rule_tac A = A and As = As in loop_free_fb_out_less_step, simp_all add: AAb)
  
          have [simp]: "Type_OK Bs"
            using Bs_def Type_OK_fb_out_less_step \<open>VarFB (Parallel_list As) = a # L\<close> \<open>Type_OK As\<close> \<open>loop_free As\<close> by blast
  
          from A have Aa: "(\<And>As ::('var, 'a) Dgr list. Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = L \<Longrightarrow> in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less L As)))"
            by simp
  
          from A have Ab: "(\<And>As ::('var, 'a) Dgr list. Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> VarFB (Parallel_list As) = L \<Longrightarrow>  io_diagram (Parallel_list (fb_less L As)))"
            by simp
  
  
          have [simp]: "VarFB (Parallel_list Bs) = L"
            apply (simp add: Bs_def)
            by (rule VarFB_fb_out_less_step, simp_all)
  
          have [simp]: "in_equiv (FB (Parallel_list Bs)) (Parallel_list (fb_less L Bs))"
            by (rule Aa, simp_all)
              
          have [simp]: "io_diagram (Parallel_list (fb_less L Bs))"
            by (rule Ab, simp_all)

          have [simp]: "in_equiv (FB (Parallel_list As)) (FB (Parallel_list Bs))"
            apply (rule in_equiv_fb_fb_less_step_TO_CHECK, simp_all)
            by (simp add: Bs_def)
 
          show "in_equiv (FB (Parallel_list As)) (Parallel_list (fb_less (a # L) As))  \<and> io_diagram (Parallel_list (fb_less (a # L) As))"
            apply (simp add: Bs_simp [THEN sym])
            apply (rule_tac B = "FB (Parallel_list Bs)" in in_equiv_tran)
            by (simp_all add: io_diagram_FB_Parallel_list)
        qed
                  
lemmas [simp] = diff_emptyset

  
lemma [simp]: "\<And> x . distinct x \<Longrightarrow> distinct y \<Longrightarrow> perm (((y \<otimes> x) @ (x \<ominus> y \<otimes> x))) x"
  by (simp add: diff_inter_right perm_switch_aux_f)
  
lemma [simp]: "io_diagram X \<Longrightarrow> perm (VarFB X @ (In X \<ominus> VarFB X)) (In X)"
  by (simp add: VarFB_def Var_def)

  
lemma Type_OK_diff[simp]: "Type_OK As \<Longrightarrow> Type_OK (As \<ominus> Bs)"
  apply (simp add: Type_OK_def, safe)
    apply (simp_all add: set_diff)
  by (metis BBB_c One_nat_def Type_OK_def Type_OK_simp inter_subset notin_inter)
    

lemma internal_fb_out_less_step: 
  assumes [simp]: "loop_free As"
    assumes [simp]: "Type_OK As"
    and [simp]: "a \<in> internal As"
  shows "internal (fb_out_less_step a As) = internal As - {a}"
  apply (subst internal_VarFB)
   apply (rule Type_OK_fb_out_less_step_new, simp_all)
  apply (subst internal_VarFB, simp_all)
  by (subst VarFB_fb_out_less_step_gen, simp_all add: set_diff)
    
end

context BaseOperationFeedbacklessVars
begin

    
lemma [simp]: "Type_OK As \<Longrightarrow> a \<in> internal As \<Longrightarrow> out (get_comp_out a As) = a"
  apply (subgoal_tac "a \<in> set (Out (get_comp_out a As))")
   apply (subst (asm) Out_out)
    apply (simp add: Type_OK_def)
  by simp_all


    
lemma internal_Type_OK_simp: "Type_OK As \<Longrightarrow> internal As = {a . (\<exists> A \<in> set As . out A = a \<and> (\<exists> B \<in> set As. a \<in> set (In B)))}"
  apply (subgoal_tac "\<And> A . A \<in> set As \<Longrightarrow> Out A = [out A]")
   apply (simp add: internal_def)
   apply auto
  using Type_OK_out by blast
    
thm Type_OK_def

lemma  Type_OK_fb_less: "\<And> As . Type_OK As \<Longrightarrow> loop_free As \<Longrightarrow> distinct x \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> Type_OK (fb_less x As)"
  proof (induction x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
      
    have [simp]: "Type_OK As"
      by (simp add: Cons)
     
    have [simp]: "a \<in> internal As"
      using Cons(5) by simp
    from this obtain A where [simp]: "A \<in> set As" and [simp]: "out A = a"
      by (subst (asm) internal_Type_OK_simp,simp_all, blast)

    show ?case
      apply simp
      apply (rule Cons(1))
         apply (rule_tac As = As in Type_OK_fb_out_less_step_new, simp_all)
        apply (rule_tac A = A in loop_free_fb_out_less_step)
           apply (simp_all add: Cons)
      using \<open>distinct (a#x)\<close> apply simp
      apply (subst internal_fb_out_less_step, simp_all add: Cons)
      using Cons.prems(3) Cons.prems(4) by auto
  qed

  
    
lemma fb_Parallel_list_fb_out_less_step: 
  assumes [simp]: "Type_OK As"
    and "Deterministic As"
    and "loop_free As"
    and internal: "a \<in> internal As"
    and X: "X = Parallel_list As"
    and Y: "Y = (Parallel_list (fb_out_less_step a As))"
    and [simp]: "perm y (In Y)"
    and [simp]: "perm z (Out Y)"
  shows "fb ([a # y \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # z]) = [y \<leadsto> In Y] oo Trs Y oo [Out Y \<leadsto> z]" and "perm (a # In Y) (In X)"
proof -
  have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> io_diagram A"
    using Type_OK_def assms(1) by blast

  define A where "A = get_comp_out a As"
  from internal have [simp]: "A \<in> set As" and [simp]: "out A = a"
    by (simp_all add: A_def)
      
  have [simp]: "get_other_out a As = As \<ominus>[A]"
    using \<open>A \<in> set As\<close> \<open>out A = a\<close> assms(1) mem_get_other_out by blast
      
  have [simp]: "length (Out A) = 1"
    using \<open>Type_OK As\<close> Type_OK_def \<open>A \<in> set As\<close> by blast
  
  have [simp]: "a \<notin> set (In A)"
    using Type_OK_loop_free_elem \<open>A \<in> set As\<close> \<open>out A = a\<close> assms(1) assms(3) by blast

  have "io_diagram Y"
    using Type_OK_fb_out_less_step_new Y assms(1) assms(3) internal io_diagram_parallel_list by blast
        
  from this have dist_a_Y: "distinct (a # In Y)"
    apply simp
    by (simp add: Y In_Parallel fb_out_less_step_def A_def [THEN sym] fb_less_step_def In_CompA set_addvars set_diff Out_out)
      
  have "io_diagram X"
    by (simp add: X io_diagram_parallel_list)
      
  from this have [simp]: "distinct (In X)"
    by (simp)
            
  from internal obtain B where [simp]: "B \<in> set As" and [simp]: "a \<in> set (In B)"
    by (simp add: internal_def, auto)
      
  have [simp]: "B \<noteq> A"
    using \<open>a \<in> set (In B)\<close> \<open>a \<notin> set (In A)\<close> by blast
      
      
  show "perm (a # In Y) (In X)"
    apply (rule set_perm)
    using dist_a_Y apply simp
      apply simp
    apply (simp add: X Y)
    apply (simp add: In_Parallel )
    apply (simp add: fb_out_less_step_def A_def [THEN sym])
    apply (simp add: fb_less_step_def In_CompA, safe)
      apply (auto simp add: set_diff set_addvars)
    using internal apply (subst (asm) internal_Type_OK_simp, simp_all)
     apply (case_tac "a \<in> set (In xa)")
      apply (auto simp add: set_diff set_addvars)
      apply (case_tac "xa = A")
    apply (drule_tac x = B in bspec, simp_all add: set_diff set_addvars)
    apply (drule_tac x = xa in bspec, simp_all add: set_diff set_addvars)
    by (case_tac "a \<in> set (In xa)", simp_all add: set_diff set_addvars Out_out)
    

  from this have [simp]: "perm (a # y) (In X)"
    apply (rule_tac y = "a # In Y" in perm_trans)
     by simp_all
      
  from this have dist_a_y: "distinct (a # y)"
    using io_diagram_distinct(1) X assms(1) dist_perm perm_sym io_diagram_parallel_list by blast
      
    
  define Z where "Z =  A \<rhd> (Parallel_list (As \<ominus> [A]))"
      
  thm fb_less_step_compA
    
  have equiv_Y_Z: "in_equiv Y Z"
    apply (simp add: Y Z_def fb_out_less_step_def A_def[THEN sym])
    apply (rule fb_less_step_compA, simp_all)
    using Deterministic_def \<open>A \<in> set As\<close> assms(2) by blast

  from this have [simp]: "perm (In Y) (In Z)" and Y_Z: "Trs Y = [In Y \<leadsto> In Z] oo Trs Z" and [simp]: "Out Z = Out Y"
    by (simp_all add: in_equiv_def)
      
  have [simp]: "perm y (In Z)"
    by (rule_tac y = "In Y" in perm_trans, simp_all)
      
  have [simp]: "io_diagram Z"
    by (metis Type_OK_def io_diagram_CompA Type_OK_diff Z_def \<open>A \<in> set As\<close> assms(1) io_diagram_parallel_list)

  have "fb ([a # y \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # z]) 
        = fb ([a # y \<leadsto> In (Parallel_list As)] oo ([In X \<leadsto> concat (map In As)] oo parallel_list (map Trs As)) oo [Out X \<leadsto> a # z])"
    by (simp add: X Trs_Parallel_list)
  also have "... = fb (([a # y \<leadsto> In X] oo [In X \<leadsto> concat (map In As)]) oo parallel_list (map Trs As) oo [Out X \<leadsto> a # z])"
    by (simp_all add: X comp_assoc TI_parallel_list TO_parallel_list Out_Parallel)
  also have "... = fb ([a # y \<leadsto> concat (map In As)] oo parallel_list (map Trs As) oo [Out X \<leadsto> a # z])"
    apply (subgoal_tac "[a # y \<leadsto> In X] oo [In X \<leadsto> concat (map In As)] = [a # y \<leadsto> concat (map In As)]")
     apply simp
    apply (subst switch_comp)
    using dist_a_y apply blast
      apply simp
    by (simp add: X In_Parallel, auto)
  also have "... =  [y \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> z]"
    thm fb_CompA
    apply (subst fb_CompA [of As A a Z _ _ _ B], simp_all add: X)
    by (simp add: Z_def)
  
  also have "... = [y \<leadsto> In Y] oo Trs Y oo [Out Y \<leadsto> z]"
    apply simp
    apply (rule_tac f = "\<lambda> X . X oo [Out Y \<leadsto> z]" in arg_cong)
    apply (simp add: Y_Z)
    apply (simp add: comp_assoc[THEN sym])
    apply (subst switch_comp, simp_all)
    using dist_a_y by auto
      
  finally show "fb ([a # y \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # z]) = [y \<leadsto> In Y] oo Trs Y oo [Out Y \<leadsto> z]"
    by simp
qed


lemma internal_In_Parallel_list: "a \<in> internal As \<Longrightarrow> a \<in> set (In (Parallel_list As))"
  by (simp add: In_Parallel internal_def)

lemma internal_Out_Parallel_list: "a \<in> internal As \<Longrightarrow> a \<in> set (Out (Parallel_list As))"
  by (simp add: Out_Parallel internal_def)
  
    
theorem fb_power_internal_fb_less: "\<And> As X Y . Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> set L \<subseteq> internal As 
  \<Longrightarrow> distinct L \<Longrightarrow>
   X = (Parallel_list As) \<Longrightarrow> Y = Parallel_list (fb_less L As) \<Longrightarrow>
   (fb ^^ length (L)) ([L @ (In X \<ominus> L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ (Out X \<ominus> L)]) = [In X \<ominus> L \<leadsto> In Y] oo Trs Y
  \<and> perm (In X \<ominus> L) (In Y)"
  proof (induction L)
    case Nil
    have [simp]: "io_diagram X"
      apply (simp add: Nil)
      by (simp add: Nil.prems(3) io_diagram_parallel_list)
    have [simp]: "Y = X"
      by (simp add: Nil)
    then show ?case
      by (simp_all add: InFB_def)
  next
    case (Cons a L)
    have type_As[simp]: "Type_OK As"
      by (simp add: Cons)
    have [simp]: "io_diagram X"
      apply (simp add: Cons)
      by (simp add: io_diagram_parallel_list)

    from type_As have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> io_diagram A"
      by (unfold Type_OK_def, simp)
        
   have internal_a[simp]: "a \<in> internal As"
     using Cons.prems(4) by auto

   have internal_a[simp]: "set L \<subseteq> internal As"
     using Cons.prems(4) by auto
        

   have "a \<in> set (In X)"
     apply (simp add: Cons)
     apply (rule internal_In_Parallel_list)
     by (simp add: Cons)
       
        
    have "set L \<subseteq> set (In X)"
     apply (simp add: Cons, safe)
      apply (rule internal_In_Parallel_list)
      using internal_a by blast
        
    have "distinct (In X)"
      by simp

    have perm_a[simp]: "perm (a # L @ (In X \<ominus> (a # L))) (In X)"
      apply (subgoal_tac "perm ((a # L) @ (In X \<ominus> (a # L))) (In X)")
       apply simp
      by (metis Cons.prems(5) \<open>a \<in> set (In X)\<close> \<open>distinct (In X)\<close> \<open>set L \<subseteq> set (In X)\<close> append_Nil diff.simps(2) diff_subset perm_switch)
        
    from this have Ba: "distinct (a # L @ (In X \<ominus> (a # L)))"
      using io_diagram_distinct(1) BaseOperationFeedbacklessVars_axioms \<open>io_diagram X\<close> dist_perm perm_sym by blast

    from perm_a and this have [simp]: "perm (L @ (In X \<ominus> (a # L))) (In X \<ominus> [a])"
    proof -
      have f1: "distinct (In X \<ominus> [a])"
        by (meson Ba dist_perm distinct_diff perm_a)
      have "{a} = set [a]"
        by (metis list.set(1) list.set(2))
      then show ?thesis
        using f1 by (metis (no_types) Ba Diff_insert_absorb distinct.simps(2) list.set(2) perm_a perm_set_eq set_diff set_perm)
    qed
      
   thm fb_Parallel_list_fb_out_less_step
     
   define Z where "Z = Parallel_list (fb_out_less_step a As)"
            
   have [simp]: "io_diagram Y"
     apply (unfold Cons)
     apply (rule io_diagram_parallel_list)
       apply (rule Type_OK_fb_less, simp_all)
     using Cons.prems(2) apply auto[1]
     using Ba by auto[1]
       
       
   have [simp]: "distinct (In X \<ominus> (a # L))"
     by (simp)

   have "io_diagram Z"
     apply (simp add: Z_def)
     apply (subst io_diagram_parallel_list, simp_all)
     by (metis Cons.prems(4) Type_OK_fb_out_less_step_new \<open>Type_OK As\<close> insert_subset list.simps(15))
       
       
   from this have dist_InZ[simp]: "distinct (In Z)"
     by simp
       

   have dist_L_InFB_X: "distinct (L @ (In X \<ominus> (a # L)))"
     apply (simp add: Cons, safe)
     using Ba apply auto[1]
     using Cons.prems(6) \<open>distinct (In X \<ominus> a # L)\<close> apply blast
     by (simp add: InFB_def set_diff)
       
   have [simp]: "perm (a # In Z) (In X)"
     apply (rule_tac fb_Parallel_list_fb_out_less_step [of As _ _ _ "In Z" "Out Z"])
     by (simp_all add: Cons Z_def)
       
   have "distinct (In X)"
     using Ba dist_perm perm_a by blast
       
   have [simp]: " perm (L @ (In X \<ominus> (a # L))) (In Z)"
     apply (rule_tac y = " (In X \<ominus> [a])" in perm_trans)
      apply (simp add: InFB_def)
       apply (subst perm_sym, simp_all)
     using \<open>distinct (In X)\<close>
     by (rule distinct_perm_cons, simp)
       
   thm concat_map_Out_get_other_out
   thm map_Out_fb_out_less_step
   thm map_Out_fb_less_step
     
   have "distinct (Out X)"
     using \<open>io_diagram X\<close> io_diagram_def by blast
       
   have "set (a # L) \<subseteq> set (Out X)"
     apply (unfold Cons)
     apply (safe)
     apply (rule internal_Out_Parallel_list)
     using Cons.prems(4) by blast
     
   have "perm (a # L @ (Out X \<ominus> (a # L))) (Out X)"
     by (metis Cons.prems(5) \<open>distinct (Out X)\<close> \<open>set (a # L) \<subseteq> set (Out X)\<close> append_Cons append_Nil diff_subset perm_switch)
       
   from this have "perm (L @ (Out X \<ominus> (a # L))) (Out X \<ominus> [a])"
     by (simp add: distinct_perm_cons)
       
   have [simp]: "distinct (Out Z)"
     by (simp add: \<open>io_diagram Z\<close>)
       
  define A where "A = get_comp_out a As"
     
  from internal_a have [simp]: "A \<in> set As" and [simp]: "out A = a"
    by (simp_all add: A_def)
      
  have get_other_out[simp]: "get_other_out a As = As \<ominus>[A]"
    using \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_other_out by blast
 
  have [simp]: "perm (L @ (Out X \<ominus> (a # L))) (Out Z)"
     apply (rule_tac y = "Out X \<ominus> [a]" in perm_trans)
     using \<open>perm (L @ (Out X \<ominus> (a # L))) (Out X \<ominus> [a])\<close> apply blast
     apply (rule set_perm)
       apply simp_all
     apply (simp add: Cons Z_def Out_Parallel del:set_map)
     apply (subst map_Out_fb_out_less_step[of A], simp_all add: set_diff)
     apply safe
       apply simp_all
       apply (case_tac "a = x", simp)
       apply (drule_tac x = aa in bspec, simp_all)
       using Cons(4)
         apply (metis Type_OK_out \<open>out A = a\<close> empty_iff list.set(1) set_ConsD)
        apply blast
         using Cons(4)
         by (simp add: A_def Type_OK_out mem_get_comp_out)

       have set_Out_Z: "set (Out Z) = set L \<union> set (Out X \<ominus> (a # L))"
         
         by (metis ListProp.perm_set_eq \<open>L @ (Out X \<ominus> a # L) <~~> Out Z\<close> set_append)
      
       have set_In_Z: "set (In Z) = set L \<union> set (In X \<ominus> (a # L))"
         by (metis ListProp.perm_set_eq \<open>L @ (In X \<ominus> a # L) <~~> In Z\<close> set_append)
      
  have [simp]: "distinct L"
    using dist_L_InFB_X by auto

  have [simp]: "set L \<subseteq> internal (fb_out_less_step a As)"
    by (metis Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)

  have [simp]: "perm (In X \<ominus> (a # L)) (In Z \<ominus> L)"
    apply (subgoal_tac "perm (L @ (In X \<ominus> (a # L))) (L @ (In Z \<ominus> L))")
     apply (metis add_left_cancel perm_mset union_code)
    apply (rule_tac y = "In Z" in perm_trans)
     apply simp
    by (metis \<open>distinct L\<close> append_Nil diff_subset dist_InZ perm_switch perm_sym set_In_Z sup_ge1)
      

  from internal_a have [simp]: "Deterministic (fb_out_less_step a As)"
    using Cons.prems(1) Deterministic_fb_out_less_step \<open>A \<in> set As\<close> \<open>out A = a\<close> type_As by blast
    
  from internal_a have [simp]: "loop_free (fb_out_less_step a As)"
    using Cons.prems(2) \<open>A \<in> set As\<close> \<open>out A = a\<close> loop_free_fb_out_less_step type_As by blast

  from internal_a have [simp]: "Type_OK (fb_out_less_step a As)"
    by (simp add: A_def Type_OK_fb_out_less_step_aux fb_out_less_step_def)
      
      
   have [simp]: "perm (In X \<ominus> (a # L)) (In Y)"
    apply (rule_tac y = "In Z \<ominus> L" in perm_trans, simp_all)
     apply (subst Cons(1) [of "fb_out_less_step a As" "Z" "Y"], simp_all)
      apply (simp add: Z_def)
     by (simp add: Cons)
       
   have [simp]: "set (In Y) \<subseteq> set (In Z \<ominus> L)"
     by (metis \<open>perm (In X \<ominus> (a # L)) (In Y)\<close> \<open>perm (In X \<ominus> (a # L)) (In Z \<ominus> L)\<close> order_refl perm_set_eq)

   have A: "(fb  ([a # L @ (In X \<ominus> (a # L)) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # L @ (Out X \<ominus> (a # L))])) = [L @ (In X \<ominus> (a # L)) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> (a # L))]"
     apply (subst fb_Parallel_list_fb_out_less_step [of As], simp_all add: Cons)
       apply (simp add: Z_def)
     by (simp_all add: Cons(7) [THEN sym])
     
   have OutFB_X_Z: "Out X \<ominus> (a # L) = Out Z \<ominus> L"
     apply (subst perm_diff_eq[of _ "a # L"])
      apply (simp add: Cons(5))
     apply (subst (2)  perm_diff_eq[of _ "L"])
      apply simp
     apply (simp add: Cons Z_def Out_Parallel)
     apply (subst map_Out_fb_out_less_step [of A], simp_all add: concat_map_Out_get_other_out del: get_other_out)
     by (meson diff_cons)
       
   have "(fb ^^ length (a # L)) ([(a # L) @ (In X \<ominus> a # L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> (a # L) @ (Out X \<ominus> a # L)]) 
      = (fb ^^ (length L)) (fb  ([a # L @ (In X \<ominus> a # L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> a # L @ (Out X \<ominus> (a # L))]))"
     by (simp add: funpow_swap1)
   also have "... = (fb ^^ length L) ([L @ (In X \<ominus> a # L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> (a # L))])"
     by (simp add: A)
   also have "... = (fb ^^ length L) (([L @ (In X \<ominus> a # L) \<leadsto> L @ (In Z \<ominus> L)] oo [L @ (In Z \<ominus> L) \<leadsto> In Z]) oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> (a # L))])"
     apply (subgoal_tac "[L @ (In X \<ominus> a # L) \<leadsto> L @ (In Z \<ominus> L)] oo [L @ (In Z \<ominus> L) \<leadsto> In Z] = [L @ (In X \<ominus> a # L) \<leadsto> In Z]")
      apply simp
     by (subst switch_comp, simp_all add: set_diff, auto)

   also have "... = (fb ^^ length L) ([L @ (In X \<ominus> a # L) \<leadsto> L @ (In Z \<ominus> L)] oo ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> a # L)]))"
     using \<open>io_diagram Z\<close> by (simp add: comp_assoc)
   
   also have "... = (fb ^^ length L) ([L \<leadsto> L] \<parallel> [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> a # L)]))"
     using dist_L_InFB_X par_switch by auto
     
       also have "... = [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo (fb ^^ length (TVs L)) ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out X \<ominus> a # L)])"
     apply (subst fb_indep_left [THEN sym])
     using \<open>io_diagram Z\<close> apply (simp add: fbtype_def )
     apply (subgoal_tac "[L \<leadsto> L] = ID (TVs L)")
       apply (simp)
     using \<open>distinct L\<close> distinct_id by blast
  
   also have "... = [(In X \<ominus> a # L) \<leadsto> (In Z \<ominus> L)] oo (fb ^^ length L) ([L @ (In Z \<ominus> L) \<leadsto> In Z] oo Trs Z oo [Out Z \<leadsto> L @ (Out Z \<ominus> L)])"
     by (simp add: OutFB_X_Z)
       
   also have "... = [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo ([In Z \<ominus> L \<leadsto> In Y] oo Trs Y)"
     apply (subst Cons(1) [of "fb_out_less_step a As" "Z" "Y"])
           apply (simp_all add: Cons)
     by (simp add: Z_def)
   also have "... = [(In X \<ominus> a # L) \<leadsto> In Z \<ominus> L] oo [In Z \<ominus> L \<leadsto> In Y] oo Trs Y"
     by (simp add:  comp_assoc)
   also have "... = [(In X \<ominus> a # L) \<leadsto> In Y] oo Trs Y"
     by (subst switch_comp, simp_all)

    finally show ?case by simp
  qed
    
  thm fb_power_internal_fb_less

    
theorem FB_fb_less:
  assumes [simp]: "Deterministic As"
    and [simp]: "loop_free As" 
    and [simp]: "Type_OK As"
    and [simp]: "perm (VarFB X) L"
    and X: "X = (Parallel_list As)"
    and Y: "Y = Parallel_list (fb_less L As)"
  shows "(fb ^^ length (L)) ([L @ InFB X \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ OutFB X]) = [InFB X \<leadsto> In Y] oo Trs Y"
    and B: "perm (InFB X) (In Y)"
proof -
  have [simp]: "set L \<subseteq> internal As"
    using assms(4) X internal_VarFB by auto
      
  have "distinct (Out (Parallel_list As))"
    by (metis Out_Parallel Type_OK_def assms(3))
      
  from this have "distinct (VarFB X)"
    by (simp add: VarFB_def X)
      
  from this have [simp]: "distinct L"
    using assms(4) dist_perm by blast

  have [simp]: "(fb ^^ length L) ([L @ (In X \<ominus> L) \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ (Out X \<ominus> L)]) = [In X \<ominus> L \<leadsto> In Y] oo Trs Y"
    and [simp]: "perm (In X \<ominus> L) (In Y)"
     apply (subst fb_power_internal_fb_less, simp_all add: X Y)
    by (subst fb_power_internal_fb_less, simp_all)
      
  have [simp]: "InFB X = In X \<ominus> L"
    by (simp add: InFB_def perm_diff_eq)
      
  have [simp]: "OutFB X = Out X \<ominus> L"
    by (simp add: OutFB_def perm_diff_eq)
      
  show "(fb ^^ length (L)) ([L @ InFB X \<leadsto> In X] oo Trs X oo [Out X \<leadsto> L @ OutFB X]) = [InFB X \<leadsto> In Y] oo Trs Y"
    by simp
  show "perm (InFB X) (In Y)"
    by simp
qed

    
definition "fb_perm_eq A = (\<forall> x. perm x (VarFB A) \<longrightarrow> 
  (fb ^^ length (VarFB A)) ([VarFB A @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> VarFB A @ OutFB A]) = 
  (fb ^^ length (VarFB A)) ([x @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> x @ OutFB A]))"
  
lemma fb_perm_eq_simp: "fb_perm_eq A = (\<forall> x. perm x (VarFB A) \<longrightarrow> 
  Trs (FB A) = (fb ^^ length (VarFB A)) ([x @ InFB A \<leadsto> In A] oo Trs A oo [Out A \<leadsto> x @ OutFB A]))"
  by (simp add: fb_perm_eq_def FB_def Let_def VarFB_def InFB_def OutFB_def)
  
lemma in_equiv_in_out_equiv: "io_diagram B \<Longrightarrow> in_equiv A B \<Longrightarrow> in_out_equiv A B"
  by (simp add: in_equiv_def in_out_equiv_def)

    
lemma [simp]: "distinct (concat (map f As)) \<Longrightarrow> distinct (concat (map f (As \<ominus> [A])))"
  apply (induction As, auto)
  by (simp add: set_diff, auto)
    

lemma set_op_list_addvars: "set (op_list [] op \<oplus> x) = (\<Union> a \<in> set x . set a)"
  by (induction x, auto simp add: set_addvars)
    
          
end

context BaseOperationFeedbacklessVars

begin
  
(*
lemma [simp]: "out B \<notin> set (In A) \<Longrightarrow> CompA B A = A"
  by (simp add: CompA_def)

lemma [simp]: "out B \<in> set (In A) \<Longrightarrow> CompA B A = B ;; A"
  by (simp add: CompA_def)
*)

lemma [simp]: "set (Out A) \<subseteq> set (In B) \<Longrightarrow> Out ((A ;; B)) = Out B"
  by (simp add: Comp_def out_def Let_def Var_def diff_eq subsetset_inter)
    
    
lemma [simp]: "set (Out A) \<subseteq> set (In B) \<Longrightarrow> out ((A ;; B)) = out B"
  by (simp add: Comp_def out_def Let_def Var_def diff_eq subsetset_inter)
    

lemma switch_par_comp3: 
  assumes [simp]: "distinct x" and
    [simp]: "distinct y"
    and [simp]: "distinct z" 
    and [simp]: "distinct u"
    and [simp]: "set y \<subseteq> set x"
    and [simp]: "set z \<subseteq> set x"
    and [simp]: "set u \<subseteq> set x"
    and [simp]: "set y' \<subseteq> set y"
    and [simp]: "set z' \<subseteq> set z" 
    and [simp]: "set u' \<subseteq> set u"
    shows "[x \<leadsto> y @ z @ u] oo [y \<leadsto> y'] \<parallel> [z \<leadsto> z'] \<parallel> [u \<leadsto> u'] = [x \<leadsto> y' @ z' @ u']"
      proof -
        have [simp]: "[x \<leadsto> y @ z @ u] = [x \<leadsto> y @ x] oo [y \<leadsto> y] \<parallel> [x \<leadsto> z @ u]"
          by (subst switch_par_comp_Subst, simp_all add:)
        show "[x \<leadsto> y @ z @ u] oo [y \<leadsto> y'] \<parallel> [z \<leadsto> z'] \<parallel> [u \<leadsto> u'] = [x \<leadsto> y' @ z' @ u']"
          apply simp
          apply (subst comp_assoc, simp_all add: par_assoc)
          apply (subst comp_parallel_distrib, simp_all)
          apply (simp add: switch_par_comp)
          apply (subst switch_par_comp, simp_all)
          using assms(10) assms(6) assms(7) assms(9) by blast
      qed
        
lemma switch_par_comp_Subst3: 
  assumes [simp]: "distinct x" and [simp]: "distinct y'" and [simp]: "distinct z'" and [simp]: "distinct t'"
    and [simp]: "set y \<subseteq> set x" and [simp]: "set z \<subseteq> set x" and [simp]: "set t \<subseteq> set x"
    and [simp]: "set u \<subseteq> set y'" and [simp]: "set v \<subseteq> set z'" and [simp]: "set w \<subseteq> set t'"
    and [simp]: "TVs y = TVs y'" and [simp]: "TVs z = TVs z'" and [simp]: "TVs t = TVs t'"
    
  shows "[x \<leadsto> y @ z @ t] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> v] \<parallel> [t' \<leadsto> w] = [x \<leadsto> Subst y' y u @ Subst z' z v @ Subst t' t w]"
proof -
  have [simp]: "[x \<leadsto> y @ z @ t] = [x \<leadsto> y @ x] oo [y' \<leadsto> y'] \<parallel> [x \<leadsto> z @ t]"
    by (subst switch_par_comp_Subst, simp_all add:)
    show "[x \<leadsto> y @ z @ t] oo [y' \<leadsto> u] \<parallel> [z' \<leadsto> v] \<parallel> [t' \<leadsto> w] = [x \<leadsto> Subst y' y u @ Subst z' z v @ Subst t' t w]"     
      apply simp
      apply (subst comp_assoc, simp_all add: par_assoc)
      apply (subst comp_parallel_distrib, simp_all)
      apply (simp add: switch_par_comp_Subst)
      apply (subst switch_par_comp_Subst, simp_all, safe)
      apply (metis Subst_set_incl assms(12) assms(6) assms(9) contra_subsetD length_TVs)
      by (metis Subst_set_incl assms(10) assms(13) assms(7) length_TVs subsetCE)
  qed
    
    
lemma Comp_assoc_single: "length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 \<Longrightarrow> out A \<noteq> out B \<Longrightarrow> io_diagram A 
  \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> out B \<notin> set (In A) \<Longrightarrow>
    deterministic (Trs A) \<Longrightarrow>
    out A \<in> set (In B) \<Longrightarrow> out A \<in> set (In C) \<Longrightarrow> out B \<in> set (In C) \<Longrightarrow> (A ;; (B ;; C)) = (A ;; B ;; (A ;; C))"
  
  apply (simp add: Comp_def Let_def Var_def , safe)
    (* using [[simp_trace=true]] *)
      apply (simp add: Out_out, safe)
             apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym])
      
            apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym])
      
           apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym] )
      
          apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym addvars_assoc [THEN sym])
 
      apply (simp add: Out_out, safe)
      apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym AAA_c addvars_assoc [THEN sym] )
      
   apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame  AAA_c diff_eq diff_addvars )
    
  apply (simp add: set_addvars set_diff set_inter addvars_minus addvars_addsame diff_sym diff_inter_left diff_inter_right addvars_assoc [THEN sym])
  apply (simp add: Out_out par_empty_left par_empty_right set_diff set_inter set_addvars)
  apply (simp add:  Out_out comp_assoc [THEN sym])
   apply (subgoal_tac " [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    Trs A \<parallel> [(In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out A # ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In B \<oplus> (In C \<ominus> [out B])] oo
    [In B \<oplus> (In C \<ominus> [out B]) \<leadsto> In B @ (In C \<ominus> [out B])] oo
    Trs B \<parallel> [In C \<ominus> [out B] \<leadsto> In C \<ominus> [out B] ] oo
    [out B # (In C \<ominus> [out B]) \<leadsto> In C]
    =
    [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
    [(In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out B # ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In A \<oplus> (In C \<ominus> [out A])] oo
    [In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo
    Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo
    [out A # (In C \<ominus> [out A]) \<leadsto> In C] ")
   apply simp
proof -
  assume [simp]: "length (Out A) = Suc 0"
  assume [simp]: "length (Out B) = Suc 0"
  assume Diff[simp]: "out A \<noteq> out B"
  assume [simp]: "io_diagram A"
  assume [simp]: "io_diagram B"
  assume [simp]: "io_diagram C"
  assume [simp]: "out A \<in> set (In B)"
  assume [simp]: "out A \<in> set (In C)"
  assume [simp]: "out B \<in> set (In C)"
  assume "out B \<notin> set (In A)"
  assume det: "deterministic (Trs A)"
    
    have [simp]: " perm (In C \<ominus> [out A] \<ominus> [out B] \<ominus> (In B \<ominus> [out A])) (In C \<ominus> [out B] \<ominus> In B)"
              proof -
          have "In C \<ominus> [out B] \<ominus> [] \<ominus> out A # (In B \<ominus> [out A]) = In C \<ominus> [out B] \<ominus> [] \<ominus> In B"
            by (meson BaseOperationFeedbacklessVars.diff_eq_set_right BaseOperationFeedbacklessVars.io_diagram_distinct(1) BaseOperationFeedbacklessVars_axioms \<open>out A \<in> set (In B)\<close> \<open>io_diagram B\<close> perm_dist_mem perm_set_eq)
          then show "perm (In C \<ominus> [out A] \<ominus> [out B] \<ominus> (In B \<ominus> [out A])) (In C \<ominus> [out B] \<ominus> In B)"
            by (metis (no_types) diff_cons diff_sym perm_refl)
        qed
          
        define a where "a = out A"
        define b where "b = out B"
        define c where "c = out C"
        define x where "x = In A"
        define y where "y = In B"
        define z where "z = In C"
        have [simp]: "distinct x"
          by (simp add: x_def)
        have [simp]: "distinct y"
          by (simp add: y_def)
        have [simp]: "distinct z"
          by (simp add: z_def)
            
        have [simp]: "b \<in> set z"
          by (simp add: b_def z_def)
        have [simp]: "b \<noteq> a"
          using Diff a_def b_def by (simp del: Diff)
            
        have X: "b \<notin> set x"
          by (simp add: \<open>out B \<notin> set (In A)\<close> b_def x_def)

        have A_det: "Trs A oo [ [a] \<leadsto> [a,a] ] = [x\<leadsto> x @ x] oo Trs A \<parallel> Trs A"
          using det apply (subst deterministicE, simp_all add: x_def a_def)
          by (simp add: Out_out)
            
        define x' where "x' = newvars (x @ y @ z) (TVs x)"
          
        have [simp]: "set x' \<inter> set x = {}" and [simp]: "set x' \<inter> set y = {}" and [simp]: "set x' \<inter> set z = {}" and [simp]: "distinct x'"
            and [simp]: "TVs x' = TVs x"
          using x'_def and newvars_old_distinct [of "(x @ y @ z)" "(TVs x)"] by auto

   have A: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
        oo [a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] 
        oo [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])] 
        oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] 
        oo [b # (z \<ominus> [b]) \<leadsto> z] = 
    [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
        oo ([a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] 
        oo [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) 
        oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] 
        oo [b # (z \<ominus> [b]) \<leadsto> z]"
    by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
      
      have B: " ... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
        oo [a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
        oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] 
        oo [b # (z \<ominus> [b]) \<leadsto> z]"
        apply (subgoal_tac "([a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] 
        oo [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) = [a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]")
            apply simp
         apply (simp add:  a_def b_def c_def x_def y_def z_def)
        apply (subst switch_comp, simp_all)
         apply (simp add: set_diff set_addvars set_inter)
        apply (simp add: addvars_def)
        apply (subgoal_tac "perm ((out A # (In B \<ominus> [out A])) @ (In C \<ominus> [out A] \<ominus> [out B] \<ominus> (In B \<ominus> [out A]))) (In B @ (In C \<ominus> [out B] \<ominus> In B))")
          apply simp
          apply (rule perm_append)
         apply (simp add: perm_dist_mem)
        by simp
 
          
      have C: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
         oo ([x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])]
         oo [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x \<oplus> (z \<ominus> [a])] oo [x \<oplus> (z \<ominus> [a]) \<leadsto> x @ (z \<ominus> [a])] 
         oo Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] 
         oo [a # (z \<ominus> [a]) \<leadsto> z]
      =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
         oo ([x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])]
         oo ([b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x \<oplus> (z \<ominus> [a])] oo [x \<oplus> (z \<ominus> [a]) \<leadsto> x @ (z \<ominus> [a])])
         oo Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] 
         oo [a # (z \<ominus> [a]) \<leadsto> z]"
        by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
          
     have D: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
         oo ([x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])]
         oo [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])]
         oo Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] 
         oo [a # (z \<ominus> [a]) \<leadsto> z]"
       apply (subgoal_tac "([b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x \<oplus> (z \<ominus> [a])] oo [x \<oplus> (z \<ominus> [a]) \<leadsto> x @ (z \<ominus> [a])]) = [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])]")
        apply simp
       apply (subst switch_comp, simp_all, safe)
        apply (simp add: set_diff set_addvars )
       apply (rule perm_cons)
         apply (simp add: set_addvars set_diff)
        apply (simp add: addvars_diff)
       by (simp add: addvars_minus)
         
     have E: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    [x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] 
    oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     Trs B \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
       apply (subst par_id_comp, simp_all)
        apply (subst TO_comp, simp_all)
         apply (subst TO_comp, simp_all)
         apply (simp add: x_def)
         apply (simp add: a_def Out_out)
        apply (simp add: y_def)
       apply (subst par_id_comp, simp_all)
        apply (subst TO_comp, simp_all)
         apply (simp add: x_def)
         apply (simp add: a_def Out_out)
       apply (subst par_id_comp, simp_all)
         apply (simp add: x_def)
         by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
     have F: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))]
    oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
     Trs B \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
         apply (subgoal_tac " [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<oplus> (y \<ominus> [a])) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    [x \<oplus> (y \<ominus> [a]) \<leadsto> x @ (y \<ominus> [a])] \<parallel> [(x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b])] = 
      [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ ((x \<ominus> [b]) \<oplus> (z \<ominus> [a] \<ominus> [b]))]")
        apply simp
       apply (subst switch_par_comp, simp_all)
       by (auto simp add: set_addvars set_diff)
         
     have "[b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] = 
        [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> (b # x) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [x \<leadsto> x] \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])]"
       apply (subst switch_par_comp, simp_all add: set_addvars set_diff X)
         apply auto [2]
       apply (subst switch_par_comp, simp_all add: set_addvars set_diff X)
         by auto
         
    from this have "Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z] =  
    (Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> (b # x) @ (z \<ominus> [a] \<ominus> [b])]) 
    oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo ([x \<leadsto> x] \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ]) oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply simp
      by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
    also have "... =  (Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [ [b] \<leadsto> [b] ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply (subst comp_parallel_distrib)
        apply (simp_all add: x_def)
      apply (subst (2) par_switch, simp_all)
      apply (simp add: set_addvars set_diff)
      using X x_def by auto
    also have "... =  
    ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply (subgoal_tac "Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [ [b] \<leadsto> [b] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]
        =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) ))")
          apply simp
      apply (subst comp_parallel_distrib)
        apply (simp_all add: b_def Out_out)
      apply (subst comp_parallel_distrib)
        apply (simp_all add: y_def Out_out)
      apply (subst switch_par_comp)
      by (simp_all add: set_diff set_addvars)
    
    also have "... =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo [b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    (Trs A \<parallel> [ b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])]) oo
    [a # (z \<ominus> [a]) \<leadsto> z]"
      apply (subgoal_tac " Trs A \<parallel> [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [a] ] =  (Trs A \<parallel> [ b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])])")
       apply simp
        apply (subst comp_parallel_distrib)
        apply (simp_all add: a_def Out_out)
      by (subst switch_comp, simp_all add: set_diff, auto)
    also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [ b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])]) oo ([ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] oo
    [a # (z \<ominus> [a]) \<leadsto> z])"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)

    also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> ([ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])])) oo ([a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a]) ] oo
    [a # (z \<ominus> [a]) \<leadsto> z])"
      apply (subgoal_tac "[ [a] \<leadsto> [a] ] \<parallel>  [b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a])] = [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a]) ]")
       apply simp
       apply (subgoal_tac "[b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> b # (z \<ominus> [a] \<ominus> [b])] = [ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]")
        apply simp
        apply (subst par_switch, simp_all add: set_diff)
      apply (subst par_switch, simp_all add: set_diff)
      using Diff a_def b_def by auto
        
    also have "... =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> ([x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> ([ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])])) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
      apply (subgoal_tac " ([a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a]) ] oo [a # (z \<ominus> [a]) \<leadsto> z]) = [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]")
        apply simp
        apply (subst switch_comp, simp_all add: set_diff)
      using Diff a_def b_def apply simp
       apply (metis \<open>b \<noteq> a\<close> \<open>distinct z\<close> \<open>out A \<in> set (In C)\<close> \<open>out B \<in> set (In C)\<close> a_def b_def distinct_diff perm_dist_mem perm_set_eq set_ConsD z_def)
      by blast
    also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] )) 
    oo ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
      by (simp add: par_assoc)
     also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
    oo (([b # x  \<leadsto> x @ [b] ] oo Trs A \<parallel> [ [b] \<leadsto> [b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
       apply (subgoal_tac " ([b # x  \<leadsto> x @ [b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
    Trs A \<parallel> [ [b] \<leadsto> [b] ] \<parallel>  [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]) =  (([b # x  \<leadsto> x @ [b] ] oo Trs A \<parallel> [ [b] \<leadsto> [b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])")
        apply simp
        apply (subst comp_parallel_distrib)
        by (simp_all add: x_def)
     also have "... =  ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
    oo (([ [b] \<leadsto> [b] ] \<parallel> Trs A oo [ [b,a] \<leadsto> [a,b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
       apply (subgoal_tac "([b # x  \<leadsto> x @ [b] ] oo Trs A \<parallel> [ [b] \<leadsto> [b] ]) = ([ [b] \<leadsto> [b] ] \<parallel> Trs A oo [ [b,a] \<leadsto> [a,b] ])")
        apply simp
         thm switch_parallel_a
         apply (cut_tac x= "[b]" and y = x and u = "[b]" and v = "[a]" and T = "Trs A" and S = "[ [b] \<leadsto> [b] ]" in switch_parallel_a)
               apply (simp_all)
           apply (simp add: X)
           by (simp_all add: x_def a_def Out_out)
      also have "... = ([ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
    oo ([ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
        apply (subgoal_tac "(([ [b] \<leadsto> [b] ] \<parallel> Trs A oo [ [b,a] \<leadsto> [a,b] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
          = ([ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])")
         apply simp
        apply (subst comp_parallel_distrib)
        by (simp_all add: a_def Out_out)
     also have "... =  [ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo (Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
    oo [ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo ([ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo 
     [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z])"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         also have "... = [ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
             oo ([ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z])"
        apply (subgoal_tac " (Trs B \<parallel> [x \<leadsto> x] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
    oo [ [b] \<leadsto> [b] ] \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) = Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
            apply simp
             apply (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out)
           by (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out)
             
    also have "... = [ y \<leadsto> y ] \<parallel> [ x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
             oo [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]"
      
      apply (subgoal_tac " ([ [b,a] \<leadsto> [a,b] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]) = [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto>  z]")
       apply (simp)
      apply (subst par_switch, simp_all add: set_diff)
      apply (subst switch_comp, simp_all add: set_diff)
       apply (simp add: perm_mset)
        by blast
        

    finally have Aa: "Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z] =  
    [y \<leadsto> y] \<parallel> [(x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
      by simp

     have G: " [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z] =  
    [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    (Trs B \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [b # (x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a])] oo
    Trs A \<parallel> [z \<ominus> [a] \<leadsto> z \<ominus> [a] ] oo
    [a # (z \<ominus> [a]) \<leadsto> z])"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
     have H: "... =   [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [(x \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo Trs B \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
      apply (simp add: Aa)
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
       
     have I:"[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] = 
        [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         
    have J:"... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
      apply (subgoal_tac " ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [y \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) = [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]")
          apply simp
      by (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out)
        have K:"... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
    [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          apply (simp add: par_assoc)
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        have L:"... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
        oo (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo  [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
        Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
       apply (subgoal_tac "((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) =  (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo  [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]")
           apply simp
      by (subst comp_parallel_distrib, simp_all add: x_def b_def Out_out a_def)
            

    have Ba: "[a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])] = 
        [ [a] \<leadsto> [a,a] ] \<parallel>  [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
          oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ [a]  ] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
          oo [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]"
      apply (subst par_switch, simp_all add: set_diff set_addvars)
        apply (cut_tac x = "a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))" and y = "[a]" and y' = "[a]" 
          and z = "a # (y \<ominus> [a])" and z' = " (y \<ominus> [a]) @ [a]" and u = "z \<ominus> [a] \<ominus> [b] " and u' = "z \<ominus> [a] \<ominus> [b]"  in switch_par_comp3)
                  apply (simp_all add: set_diff set_addvars)
        apply auto
      apply (cut_tac x = "a # ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))" 
          and y = "a # (y \<ominus> [a])" and y' = y and z = "a # (z \<ominus> [a] \<ominus> [b])" and z' = "z \<ominus> [b]"  in switch_par_comp)
      by (simp_all add:set_diff set_addvars, auto)
        
    have Ca: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    ([ [a] \<leadsto> [a, a] ] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
     [a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]) oo
    Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo
    [b # (z \<ominus> [b]) \<leadsto> z] = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo
    [ [a] \<leadsto> [a, a] ] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
     ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo
    Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo
    [b # (z \<ominus> [b]) \<leadsto> z])"
      by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
    have Da: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        ([a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z])"
      apply (subgoal_tac " (Trs A \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [ [a] \<leadsto> [a, a] ] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) = 
        (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]")
       apply simp
      by (subst comp_parallel_distrib, simp_all add: a_def Out_out)
        
    have Ea: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        (([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]  oo [b # (z \<ominus> [b]) \<leadsto> z])"
      apply (subgoal_tac "[a # (y \<ominus> [a]) \<leadsto> y] \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] = ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ]")
       apply simp
      by (subst comp_parallel_distrib, simp_all add: y_def)
    have Fa: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        (([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo [ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z])"
      apply (subgoal_tac "([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] 
          = ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo [ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] ")
       apply simp
      apply (subst comp_parallel_distrib, simp_all)
       apply (subst TO_comp, simp_all add: y_def b_def Out_out)
      by (subst switch_comp, simp_all add: set_diff, auto)
        
     have Ga: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo ([ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z])"
       by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         have Ha: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A oo [ [a] \<leadsto> [a, a] ] ) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
        oo [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
        ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b]) ] oo ([ b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
           apply (subgoal_tac " ([ [b] \<leadsto> [b] ] \<parallel> [ a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z]) = ([ b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])")
            apply simp
           apply (subst par_switch, simp_all add:set_diff, auto)
           apply (subst switch_comp, simp_all add: set_diff)
            apply (rule set_perm , simp_all add: set_diff, auto)
           using a_def z_def apply auto[1]
           using \<open>b \<noteq> a\<close> by auto
             
       
         have Ab: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo ([x \<leadsto> x @ x] oo Trs A \<parallel> Trs A) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]
        = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (([x \<leadsto> x @ x] oo Trs A \<parallel> Trs A) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])])"
           by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
         have Ac: "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo 
            (([x \<leadsto> x @ x] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> Trs A \<parallel> ([(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])])))"
           apply (subgoal_tac "(([x \<leadsto> x @ x] oo Trs A \<parallel> Trs A) \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) = 
               (([x \<leadsto> x @ x] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> Trs A \<parallel> ([(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])])))")
            apply simp
           apply (subst comp_parallel_distrib, simp_all)
            apply (simp add: x_def)
           by (subst switch_par_comp, simp_all)
         have Ad: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ ((y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo 
            [x \<leadsto> x @ x] \<parallel> [(y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> Trs A \<parallel> [(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])]"
           by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def par_assoc)
         have Ae: "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ ((y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> Trs A \<parallel> [(y \<ominus> [a]) \<leadsto> y \<ominus> [a] ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto>  (z \<ominus> [a] \<ominus> [b])]"
           by (subst switch_par_comp, simp_all add: set_addvars set_diff, auto)
           
           
         have "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
              oo Trs A \<parallel> Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
              = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo (Trs A \<parallel> (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
            ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
           apply (simp add: par_assoc)
           by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo Trs A \<parallel> (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ]) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
          
           apply (subst comp_parallel_distrib, simp_all add: a_def Out_out)
          by (subst comp_parallel_distrib, simp_all add: a_def Out_out)
            
         also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo Trs A \<parallel> ([ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] oo [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
           apply (subgoal_tac "(Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ]) 
            = ([ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] oo [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A)")
            apply simp
           apply (subst switch_parallel_a [THEN sym], simp_all add: set_diff)
           using \<open>set x' \<inter> (set y) = {}\<close> apply blast
           by (simp_all add: Out_out a_def x_def)
             
        also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo ([x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
                    oo  Trs A \<parallel> ([y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]"
          apply (subgoal_tac " Trs A \<parallel> ([ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] oo [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
              = ([x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
                    oo  Trs A \<parallel> ([y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> Trs A) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])")
           apply simp
           apply (subst comp_parallel_distrib, simp_all add: a_def Out_out x_def)
          by (subst comp_parallel_distrib, simp_all add: x_def)
            also have "... = ([x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
                oo [x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
                    oo  ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])])"
           apply (simp add: par_assoc)
              by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
                
          also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] 
                    oo  ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ]) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])])"
            
           apply (subgoal_tac "([x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (x @ (y \<ominus> [a])) @ (z \<ominus> [a] \<ominus> [b])] 
                oo [x \<leadsto> x] \<parallel> [ x' @ (y \<ominus> [a])  \<leadsto> (y \<ominus> [a]) @ x'  ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
              = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] ")
             apply simp
            apply (subst switch_par_comp_Subst3, simp_all add: set_diff set_addvars)
              apply (simp add: Diff_Int_distrib, blast)
            apply (subgoal_tac " Subst (x' @ (y \<ominus> [a])) (x @ (y \<ominus> [a])) ((y \<ominus> [a]) @ x') = (y \<ominus> [a]) @ x")
             apply simp
            apply (simp add: Subst_append, safe)
             apply (metis (no_types, lifting) AAA_c Subst_eq Subst_not_in_a TVs_length_eq \<open>TVs x' = TVs x\<close> \<open>set x' \<inter> set y = {}\<close> disjoint_insert(2) empty_set insert_Diff list.simps(15) set_diff)
            by (metis Subst_all Subst_cancel_left_type TVs_length_eq \<open>TVs x' = TVs x\<close> \<open>set x' \<inter> set y = {}\<close> empty_inter_diff empty_set newvars_distinct set_inter x'_def)
              
        also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] 
                    oo  (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
          
          apply (subst comp_parallel_distrib)
            apply (simp_all add: y_def a_def Out_out)[2]
          apply (subst comp_switch_id)
            apply (simp_all add: set_diff a_def Out_out) [2]
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
            
       finally have Bc: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ x @ (y \<ominus> [a]) @ (z \<ominus> [a] \<ominus> [b])] 
              oo Trs A \<parallel> Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              [ [a] \<leadsto> [a] ] \<parallel> [a # (y \<ominus> [a]) \<leadsto> (y \<ominus> [a]) @ [a] ] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo
              ([a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> [a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> a # (z \<ominus> [a] \<ominus> [b])]
            = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] 
                    oo  (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> (Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
         by simp
           
              
     have "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] = 
        [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
        ([x \<leadsto> x] \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> ([x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])])) oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]"
       apply (subgoal_tac " (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] = 
          ([x \<leadsto> x] \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> ([x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]))")
        apply simp
       apply (subst comp_parallel_distrib)
         apply (simp_all add: x_def y_def a_def Out_out) [2]
       apply (simp add: distinct_id)
       by (subst comp_id_left_simp, simp_all add: x_def a_def Out_out)
     also have " ... =  ([x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
        [x \<leadsto> x] \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])]) oo
    ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
       apply (simp add: par_assoc)
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
     also have "... = [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] oo
    ((Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<leadsto> x ] \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])"
       by (subst switch_par_comp3, simp_all add: set_diff set_addvars, auto)
         
    also have "... =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]"
      apply (subst comp_parallel_distrib)
        apply (simp_all add: Out_out a_def b_def c_def x_def y_def z_def) [2]
      apply (subst comp_parallel_distrib)
        apply (simp_all add: Out_out a_def b_def c_def x_def y_def z_def) [2]
      by (simp add: x_def)
        
    finally have Cc: "[x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ (x \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y]) \<parallel> [x \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (z \<ominus> [a] \<ominus> [b])] oo
    Trs B \<parallel> Trs A \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] =  [x \<oplus> (y \<ominus> [a]) \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<ominus> [a]) @ x @ (z \<ominus> [a] \<ominus> [b])] oo
    (Trs A \<parallel> [y \<ominus> [a] \<leadsto> y \<ominus> [a] ] oo [a # (y \<ominus> [a]) \<leadsto> y] oo Trs B) \<parallel> Trs A \<parallel> [(z \<ominus> [a] \<ominus> [b]) \<leadsto> (z \<ominus> [a] \<ominus> [b])]"
      by simp
         
     show "[In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    Trs A \<parallel> [(In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out A # ((In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In B \<oplus> (In C \<ominus> [out B])] oo
    [In B \<oplus> (In C \<ominus> [out B]) \<leadsto> In B @ (In C \<ominus> [out B])] oo
    Trs B \<parallel> [In C \<ominus> [out B] \<leadsto> In C \<ominus> [out B] ] oo
    [out B # (In C \<ominus> [out B]) \<leadsto> In C] =
    [In A \<oplus> (In B \<ominus> [out A]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<oplus> (In B \<ominus> [out A])) @ ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]))] oo
    ([In A \<oplus> (In B \<ominus> [out A]) \<leadsto> In A @ (In B \<ominus> [out A])] oo Trs A \<parallel> [In B \<ominus> [out A] \<leadsto> In B \<ominus> [out A] ] oo [out A # (In B \<ominus> [out A]) \<leadsto> In B] oo Trs B) \<parallel>
    [(In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> (In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])] oo
    [out B # ((In A \<ominus> [out B]) \<oplus> (In C \<ominus> [out A] \<ominus> [out B])) \<leadsto> In A \<oplus> (In C \<ominus> [out A])] oo
    [In A \<oplus> (In C \<ominus> [out A]) \<leadsto> In A @ (In C \<ominus> [out A])] oo
    Trs A \<parallel> [In C \<ominus> [out A] \<leadsto> In C \<ominus> [out A] ] oo
    [out A # (In C \<ominus> [out A]) \<leadsto> In C]"
       apply (simp add: a_def [THEN sym] b_def [THEN sym] c_def [THEN sym] x_def [THEN sym] y_def [THEN sym] z_def [THEN sym])
       apply (simp add: A B C D E F)
       apply (simp add: X AAA_c)
       apply (simp add: G H I J K L)
       apply (simp add: Ba )
       apply (simp add: Ca Da Ea Fa Ga Ha)
         thm arg_cong
       apply (subst  arg_cong [of _ _ "\<lambda> A . A oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"], simp_all)
       apply (simp add: A_det)
       apply (subst Ab)
         apply (simp add: Ac Ad Ae)
         apply (simp add: Bc Cc)
         by (simp add: par_assoc)
     qed
         
lemma Comp_commute_aux:
  assumes [simp]: "length (Out A) = 1"
    and [simp]: "length (Out B) = 1"
    and [simp]: "io_diagram A"
    and [simp]: "io_diagram B"
    and [simp]: "io_diagram C"
    and [simp]: "out B \<notin> set (In A)"
    and [simp]: "out A \<notin> set (In B)"
    and [simp]: "out A \<in> set (In C)"
    and [simp]: "out B \<in> set (In C)"
    and Diff: "out A \<noteq> out B"

    shows "Trs (A ;; (B ;; C)) = 
                [In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ In B @ (In C \<ominus> [out A] \<ominus> [out B])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ In C \<ominus> [out A] \<ominus> [out B] \<leadsto> In C \<ominus> [out A] \<ominus> [out B] ]
                    oo [out A # out B # (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In C] 
                    oo Trs C"
      and "In (A ;; (B ;; C)) = In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B])"
      and "Out (A ;; (B ;; C)) = Out C"
    proof -
        define a where "a = out A"
        define b where "b = out B"
        define c where "c = out C"
        define x where "x = In A"
        define y where "y = In B"
        define z where "z = In C"
        have [simp]: "distinct x"
          by (simp add: x_def)
        have [simp]: "distinct y"
          by (simp add: y_def)
        have [simp]: "distinct z"
          by (simp add: z_def)
            
        have [simp]: "b \<in> set z"
          by (simp add: b_def z_def)
        have [simp]: "b \<noteq> a"
          using Diff a_def b_def by (simp)
        have [simp]: "a \<noteq> b"
          using Diff a_def b_def by (simp)
        have [simp]: "b \<notin> set x"
          by (simp add: b_def x_def)
            
        have [simp]: "a \<notin> set y"
          by (simp add: a_def y_def)
            
        have [simp]: "a \<in> set z"
          by (simp add: \<open>a \<equiv> out A\<close> \<open>z \<equiv> In C\<close>)
            
        have [simp]: "(y \<oplus> (z \<ominus> [b])) \<ominus> [a] = y \<oplus> (z \<ominus> [a] \<ominus> [b])"
          by (simp add: AAA_c addvars_minus diff_sym)
            
            
        have "[y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] 
            = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo ([y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo ([y @ [a] \<leadsto> a # y] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          apply (subgoal_tac " ([y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) = 
                ([y @ [a] \<leadsto> a # y] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B) \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
           apply simp
          by (subst comp_parallel_distrib, simp_all add: y_def)
          also have "... = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo (Trs B \<parallel> [ [a] \<leadsto> [a] ] oo [ [b, a] \<leadsto> [a, b] ])  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
            apply (subgoal_tac "([y @ [a] \<leadsto> a # y] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B)  = (Trs B \<parallel> [ [a] \<leadsto> [a] ] oo [ [b, a] \<leadsto> [a, b] ])")
             apply simp
            thm switch_parallel_a
            apply (cut_tac switch_parallel_a [of y "[a]" "[b]" "[a]" "Trs B" "[ [a] \<leadsto> [a] ]"])
                  apply simp_all
             by (simp_all add: y_def b_def Out_out)
              also have "... =  [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo (Trs B \<parallel> [ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
                apply (subgoal_tac "(Trs B \<parallel> [ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
                    =   (Trs B \<parallel> [ [a] \<leadsto> [a] ] oo [ [b, a] \<leadsto> [a, b] ])  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
                apply simp
                by (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out)
          also have "... = ([y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo Trs B \<parallel> ([ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])) oo ([ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
            apply (simp add: par_assoc)
            by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
              also have "... =  Trs B \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo  ([ [b, a] \<leadsto> [a, b] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
                apply (subgoal_tac "([y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo Trs B \<parallel> ([ [a] \<leadsto> [a] ]  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])) = Trs B \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] ")
                 apply simp
                apply (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out)
                by (subst par_switch, simp_all add: set_diff)
        also have "... =  Trs B \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          apply (subst par_switch)
             apply (simp_all add: set_diff)
          apply (subst switch_comp, simp_all add: set_diff)
          by (subst set_perm, simp_all add: set_diff, auto)
        also have "... =  (Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [ [b] \<leadsto> [b] ] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])])oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]"
          by (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out)
        also have "... = Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo ([ [b] \<leadsto> [b] ] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo  [b # a # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z])"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... = Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z]"
          apply (subst par_switch, simp_all add: set_diff, auto)
          apply (subst switch_comp, simp_all add: set_diff, auto)
          by (rule set_perm, simp_all add: set_diff, auto)
            
        finally have Aa: "Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] = [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] 
            oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] 
            oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z]" (is "?X = ?Y")
          by simp
            
        have "Trs (A ;; (B ;; C)) = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] oo
            ([y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])] oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] oo Trs C  )"       
          by (simp add: Comp_def Let_def a_def [THEN sym] x_def [THEN sym] b_def [THEN sym] y_def [THEN sym]
              c_def [THEN sym] z_def [THEN sym] Var_def Out_out par_empty_left set_addvars set_diff addvars_assoc [THEN sym])
        also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo ([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] oo
            [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] oo Trs C"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
            also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
                  oo Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z] oo Trs C"
              apply (subgoal_tac "([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y \<oplus> (z \<ominus> [b])] oo
            [y \<oplus> (z \<ominus> [b]) \<leadsto> y @ (z \<ominus> [b])]) = [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]")
               apply simp
              apply (subst switch_comp)
                 apply (simp_all add: set_addvars set_diff)
              by (subst set_perm, simp_all add: set_addvars set_diff, auto)
          also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
                  oo (Trs B \<parallel> [z \<ominus> [b] \<leadsto> z \<ominus> [b] ] oo [b # (z \<ominus> [b]) \<leadsto> z]) oo Trs C"
            by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
          also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
            oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])]
                  oo ?Y oo Trs C"
            by (simp add: Aa)
          also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo ([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])] oo
                [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) 
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
            by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
           also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  a # y @ (z \<ominus> [a] \<ominus> [b]) ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
            apply (subgoal_tac "([a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto> y @ (z \<ominus> [b])] oo
                [y \<leadsto> y] \<parallel> [z \<ominus> [b] \<leadsto> a # (z \<ominus> [a] \<ominus> [b])] oo [y @ [a] \<leadsto> a # y] \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ])  = 
                [a # (y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  a # y @ (z \<ominus> [a] \<ominus> [b]) ]")
              apply (simp)
             apply (subst switch_par_comp, simp_all add: set_diff set_addvars, auto)
               thm switch_par_comp
               apply (cut_tac switch_par_comp [of "a # (y \<oplus> (z \<ominus> [a] \<ominus> [b]))" " y @ [a]" "(z \<ominus> [a] \<ominus> [b])" "a # y"])
                      apply simp
               by (simp_all add: set_addvars set_diff, auto)
             
            also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [ [a] \<leadsto> [a] ] \<parallel> [(y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  y @ (z \<ominus> [a] \<ominus> [b]) ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
              apply (subst par_switch)
              by (simp_all add: set_diff set_addvars)
                also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo (Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [ [a] \<leadsto> [a] ] \<parallel> [(y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  y @ (z \<ominus> [a] \<ominus> [b]) ])
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                  by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
              also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] oo Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] 
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                apply (subgoal_tac "(Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> (z \<ominus> [a] \<ominus> [b])] 
              oo [ [a] \<leadsto> [a] ] \<parallel> [(y \<oplus> (z \<ominus> [a] \<ominus> [b])) \<leadsto>  y @ (z \<ominus> [a] \<ominus> [b]) ]) =  Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] ")
                 apply simp
                by (subst comp_parallel_distrib, simp_all add: y_def b_def Out_out a_def)
                  
                  
              also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
                  oo ([x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> ( [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]))
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                
                apply (subgoal_tac "Trs A \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])]  = ([x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> ( [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]))")
                 apply simp
                apply (subst comp_parallel_distrib)
                  apply (simp_all add: y_def b_def Out_out x_def) [2]
                by (subst switch_par_comp, simp_all add: x_def)
               also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
                  oo [x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                apply (simp add: par_assoc) 
                 by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
            also have "... =  ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])]) oo (Trs A \<parallel> [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
              apply (subgoal_tac " ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ (y \<oplus> (z \<ominus> [a] \<ominus> [b]))] 
                  oo [x \<leadsto> x] \<parallel> [y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ (z \<ominus> [a] \<ominus> [b])]) = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])]) ")
              apply simp
              by (subst switch_par_comp, simp_all add: set_diff set_addvars, auto)
           also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])]) oo Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
                apply (subgoal_tac " (Trs A \<parallel> [y \<leadsto> y] \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                oo [ [a] \<leadsto> [a] ] \<parallel> Trs B \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]) =  Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]")
              apply simp
                apply (subst comp_parallel_distrib)
                  apply (simp_all add: y_def b_def Out_out x_def a_def)
             by (subst comp_parallel_distrib, simp_all add: Out_out)
        
           finally have "Trs (A ;; (B ;; C)) = 
                [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                    oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] 
                    oo Trs C"
             by simp
               
        from this show "Trs (A ;; (B ;; C)) = 
                [In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In A @ In B @ (In C \<ominus> [out A] \<ominus> [out B])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ In C \<ominus> [out A] \<ominus> [out B] \<leadsto> In C \<ominus> [out A] \<ominus> [out B] ]
                    oo [out A # out B # (In C \<ominus> [out A] \<ominus> [out B]) \<leadsto> In C] 
                    oo Trs C"
          by (simp add: x_def y_def z_def a_def b_def)
        show "In (A ;; (B ;; C)) = In A \<oplus> In B \<oplus> (In C \<ominus> [out A] \<ominus> [out B])"
          apply (simp add: Comp_def Let_def Var_def Out_out set_addvars set_diff, safe)
           apply (metis \<open>a \<equiv> out A\<close> \<open>b \<equiv> out B\<close> \<open>y \<oplus> (z \<ominus> [b]) \<ominus> [a] = y \<oplus> (z \<ominus> [a] \<ominus> [b])\<close> addvars_assoc b_def y_def z_def) 
            by (simp add: Diff)
          
      show  "Out (A ;; (B ;; C)) = Out C"
          apply (simp add: Comp_def Let_def Var_def Out_out set_addvars set_diff, safe)
            by (simp add: Diff)
  qed

       
lemma Comp_commute:
  assumes [simp]: "length (Out A) = 1"
    and [simp]: "length (Out B) = 1"
    and [simp]: "io_diagram A"
    and [simp]: "io_diagram B"
    and [simp]: "io_diagram C"
    and [simp]: "out B \<notin> set (In A)"
    and [simp]: "out A \<notin> set (In B)"
    and [simp]: "out A \<in> set (In C)"
    and [simp]: "out B \<in> set (In C)"
    and Diff: "out A \<noteq> out B"
  shows "in_equiv (A ;; (B ;; C)) (B ;; (A ;; C))"
    proof -
        define a where "a = out A"
        define b where "b = out B"
        define c where "c = out C"
        define x where "x = In A"
        define y where "y = In B"
        define z where "z = In C"
        have [simp]: "distinct x"
          by (simp add: x_def)
        have [simp]: "distinct y"
          by (simp add: y_def)
        have [simp]: "distinct z"
          by (simp add: z_def)
            
        have [simp]: "b \<in> set z"
          by (simp add: b_def z_def)
        have [simp]: "b \<noteq> a"
          using Diff a_def b_def by (simp)
        have [simp]: "a \<noteq> b"
          using Diff a_def b_def by (simp)
        have [simp]: "b \<notin> set x"
          by (simp add: b_def x_def)
            
        have [simp]: "a \<notin> set y"
          by (simp add: a_def y_def)
            
        have [simp]: "a \<in> set z"
          by (simp add: \<open>a \<equiv> out A\<close> \<open>z \<equiv> In C\<close>)
            
        have [simp]: "(y \<oplus> (z \<ominus> [b])) \<ominus> [a] = y \<oplus> (z \<ominus> [a] \<ominus> [b])"
          by (simp add: AAA_c addvars_minus diff_sym)
            
        
        have A: "Trs (A ;; (B ;; C)) = 
                [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])] 
                    oo Trs A \<parallel> Trs B \<parallel> [ z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ]
                    oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] 
                    oo Trs C"
          apply (subst Comp_commute_aux, simp_all)
           apply (simp add: Diff)
          by (simp add: x_def y_def z_def a_def b_def)
            
            
        define x' where "x' = newvars (y) (TVs x)"
          
        have [simp]: "distinct x'" and [simp]: "set y \<inter> set x' = {}"
           by (simp_all add: x'_def)
            
            
        have  " [In (A ;; (B ;; C)) \<leadsto> In (B ;; (A ;; C))] oo Trs (B ;; (A ;; C)) = 
              [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a])]
              oo ([y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])] 
              oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C)"
          apply (subst Comp_commute_aux, simp_all)
          using Diff apply auto
          apply (subst Comp_commute_aux, simp_all)
          apply (subst Comp_commute_aux, simp_all)
          by (simp add: x_def[THEN sym] y_def[THEN sym] z_def[THEN sym] a_def[THEN sym] b_def[THEN sym])
            
        also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a])]
              oo [y \<oplus> x \<oplus> (z \<ominus> [b] \<ominus> [a]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          by (simp add:  Out_out comp_assoc a_def b_def c_def x_def y_def z_def)
        also have "... =  ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo Trs B \<parallel> Trs A \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          apply (subst switch_comp, simp_all)
          by (rule set_perm, simp_all add: set_addvars set_diff, auto)
            also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo ([y @ x' \<leadsto> x' @ y] oo Trs A \<parallel> Trs B oo [ [a, b] \<leadsto> [b, a] ]) \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
              
              apply (subgoal_tac "Trs B \<parallel> Trs A = ([y @ x' \<leadsto> x' @ y] oo Trs A \<parallel> Trs B oo [ [a] @ [b] \<leadsto> [b] @ [a] ])")
               apply simp
              apply (subst switch_par [THEN sym], simp_all)
              by (simp_all add: y_def x'_def x_def b_def a_def Out_out)
        also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])])
              oo ([y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo [ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) 
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          
          apply (subgoal_tac "([y @ x' \<leadsto> x' @ y] oo Trs A \<parallel> Trs B oo [ [a, b] \<leadsto> [b, a] ]) \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]  = 
               ([y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo [ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) ")
           apply simp
          apply (subst comp_parallel_distrib)
            apply (simp_all add: Out_out x'_def x_def y_def) [2]
          apply (subst comp_parallel_distrib)
          by (simp_all add: Out_out x'_def x_def y_def b_def a_def)
            
        also have "... = ([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> y @ x @ (z \<ominus> [b] \<ominus> [a])]
              oo [y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo ([ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]) oo Trs C"
          by (simp add:  Out_out comp_assoc a_def b_def x_def y_def z_def x'_def)
        also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [b] \<ominus> [a])]
               oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] oo ([ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]) oo Trs C"
          apply (subgoal_tac "([x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> (y @ x) @ (z \<ominus> [b] \<ominus> [a])]
              oo [y @ x' \<leadsto> x' @ y]  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]) = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [b] \<ominus> [a])]")
           apply simp
            thm switch_par_comp_Subst
            apply (subst switch_par_comp_Subst)
                     apply (simp_all add: set_addvars set_diff, auto) [9]
             apply (simp add: x'_def)
            apply (simp add: Subst_append)
              apply (subgoal_tac "Subst (y @ x') (y @ x) x' = x")
             apply (subgoal_tac "Subst (y @ x') (y @ x) y = y")
              apply simp
             apply (metis Subst_eq Subst_not_in \<open>distinct x'\<close> \<open>distinct y\<close> \<open>set y \<inter> set x' = {}\<close> dist_perm distinct_append length_Subst perm_tp)
              by (simp add: \<open>x' \<equiv> newvars y (TVs x)\<close>)
            
        also have "... =  [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [b] \<ominus> [a])]
               oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ] 
              oo [a # b # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z] oo Trs C"
          apply (subgoal_tac "([ [a, b] \<leadsto> [b, a] ] \<parallel> [z \<ominus> [b] \<ominus> [a] \<leadsto> z \<ominus> [b] \<ominus> [a] ]
              oo [b # a # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]) = [a # b # (z \<ominus> [b] \<ominus> [a]) \<leadsto> z]")
           apply simp
          apply (subst par_switch, simp_all add: set_diff)
          apply (subst switch_comp, simp_all add: set_addvars set_diff)
          by (rule set_perm, auto simp add: set_diff)
        also have "... = [x \<oplus> y \<oplus> (z \<ominus> [a] \<ominus> [b]) \<leadsto> x @ y @ (z \<ominus> [a] \<ominus> [b])] oo Trs A \<parallel> Trs B  \<parallel> [z \<ominus> [a] \<ominus> [b] \<leadsto> z \<ominus> [a] \<ominus> [b] ] oo [a # b # (z \<ominus> [a] \<ominus> [b]) \<leadsto> z] oo Trs C"
          by (simp add: diff_sym)
          
            
        finally have [simp]: "Trs (A ;; (B ;; C)) = [In (A ;; (B ;; C)) \<leadsto> In (B ;; (A ;; C))] oo Trs (B ;; (A ;; C))"
          apply (simp)
          by (simp add: A)
            
        have [simp]: "Out (A ;; (B ;; C)) = Out (B ;; (A ;; C))"
          apply (subst Comp_commute_aux, simp_all)
           apply (simp add: Diff)
          apply (subst Comp_commute_aux, simp_all)
           using Diff by auto
            
        have [simp]: "perm (In (A ;; (B ;; C))) (In (B ;; (A ;; C)))"
          apply (subst Comp_commute_aux, simp_all)
           apply (simp add: Diff)
          apply (subst Comp_commute_aux, simp_all)
          using Diff apply auto
            by (simp add: diff_sym distinct_perm_switch)

        show "in_equiv (A ;; (B ;; C)) (B ;; (A ;; C))"
          by (simp add: in_equiv_def)
  qed

lemma CompA_commute_aux_a: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 
    \<Longrightarrow> out A \<notin> set (Out C) \<Longrightarrow> out B \<notin> set (Out C)
    \<Longrightarrow> out A \<noteq> out B \<Longrightarrow> out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A)
    \<Longrightarrow> deterministic (Trs A)
    \<Longrightarrow> (CompA (CompA B A) (CompA B C)) = (CompA (CompA A B) (CompA A C))"
  proof -
    assume [simp]: "io_diagram A"
    assume [simp]: "io_diagram B"
    assume [simp]: "io_diagram C"
    assume "length (Out A) = 1"
    assume "length (Out B) = 1"
    assume [simp]: "out A \<notin> set (Out C)"
    assume [simp]: "out B \<notin> set (Out C)"
    assume B: "out A \<noteq> out B"
    assume [simp]: "deterministic (Trs A)"
      
    have [simp]: "Out A = [out A]"
      using Out_out \<open>length (Out A) = 1\<close> by auto
    have [simp]: "Out B = [out B]"
      using Out_out \<open>length (Out B) = 1\<close> by auto
    have [simp]: "io_diagram (A ;; C)"
      by (rule io_diagram_Comp, simp_all)
    assume A[simp]: "out A \<in> set (In B)"
    assume [simp]: "out B \<notin> set (In A)"
      
    have [simp]: "io_diagram (B ;; C)"
      by (rule io_diagram_Comp, simp_all)
    have [simp]: "io_diagram (A ;; (B ;; C))"
      apply (rule io_diagram_Comp, simp_all)
      by (simp add: Comp_def Let_def Var_def set_addvars set_diff)
    then show ?thesis
      apply (simp)
        proof (cases "out A \<in> set (In C)")
          case True
          from True have [simp]: "out A \<in> set (In C)"
            by simp
          have [simp]: "out A \<in> set (In (CompA B C))"
            by (simp add: In_CompA set_addvars)
          then show "(CompA A (CompA B C)) = (CompA (A ;; B) (CompA A C))"
            apply (simp)
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out ((A ;; B)) \<in> set (In (A ;; C))"
              apply (simp)
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def True)
            then show "(A ;; CompA B C) = (CompA (A ;; B) (A ;; C))" 
              apply (simp add: True)
              apply (rule  Comp_assoc_single, simp_all)
              using B apply blast
                using True by blast
          next
            case False
            have [simp]: "out ((A ;; B)) \<notin> set (In (A ;; C))"
              apply (simp)
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def False)
            then show "(A ;; CompA B C) = (CompA (A ;; B) (A ;; C))"
              by (simp add: False)
          qed
        next
          case False
          assume [simp]: "out A \<notin> set (In C)"
          then show "(CompA A (CompA B C)) = (CompA (A ;; B) (CompA A C))"
            apply simp
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out (A ;; B) \<in> set (In C)"
              by (simp add: True)
            have [simp]: "out A \<in> set (In (B ;; C))"
              by (simp add: Comp_def Let_def set_addvars)
            then show "(CompA A (CompA B C)) = (CompA (A ;; B) C)" 
              by (simp add: True Comp_assoc_new in_equiv_eq)
          next
            case False
            have [simp]: "out (A ;; B) \<notin> set (In C)"
              using False by simp
            then show "(CompA A (CompA B C)) = (CompA (A ;; B) C)" 
              by (simp add: False in_equiv_eq)
          qed
        qed
  qed

    
lemma CompA_commute_aux_b: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> io_diagram C \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 
    \<Longrightarrow> out A \<notin> set (Out C) \<Longrightarrow> out B \<notin> set (Out C)
    \<Longrightarrow> out A \<noteq> out B \<Longrightarrow> out A \<notin> set (In B) \<Longrightarrow> out B \<notin> set (In A)
    \<Longrightarrow> in_equiv (CompA (CompA B A) (CompA B C)) (CompA (CompA A B) (CompA A C))"
  proof -
    assume [simp]: "io_diagram A"
    assume [simp]: "io_diagram B"
    assume [simp]: "io_diagram C"
    assume "length (Out A) = 1"
    assume "length (Out B) = 1"
    assume [simp]: "out A \<notin> set (Out C)"
    assume [simp]: "out B \<notin> set (Out C)"
    assume B: "out A \<noteq> out B"
      
    have [simp]: "Out A = [out A]"
      using Out_out \<open>length (Out A) = 1\<close> by auto
    have [simp]: "Out B = [out B]"
      using Out_out \<open>length (Out B) = 1\<close> by auto
    have [simp]: "io_diagram (A ;; C)"
      by (rule io_diagram_Comp, simp_all)
        
    assume A[simp]: "out A \<notin> set (In B)"
    assume [simp]: "out B \<notin> set (In A)"
      
    have [simp]: "io_diagram (B ;; C)"
      by (rule io_diagram_Comp, simp_all)
        (*
    have [simp]: "io_diagram (A ;; (B ;; C))"
      apply (rule io_diagram_Comp_a, simp_all)
      by (simp add: Comp_def Let_def Var_def set_addvars set_diff)
*)
    then show ?thesis
      apply (simp)
        proof (cases "out A \<in> set (In C)")
          case True
          from True have [simp]: "out A \<in> set (In C)"
            by simp
          have [simp]: "out A \<in> set (In (CompA B C))"
            apply (simp add: In_CompA set_addvars set_diff)
              using B by blast
          then show "in_equiv (CompA A (CompA B C)) (CompA B (CompA A C))"
            apply (simp)
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out B \<in> set (In (A ;; C))"
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def True)
            then show "in_equiv (A ;; CompA B C) (CompA B (A ;; C))" 
              apply (simp add: True)
                thm Comp_commute
                apply (subst Comp_commute, simp_all)
                 apply (simp add: True)
                  by (simp add: B)
          next
            case False
            have [simp]: "out B \<notin> set (In (A ;; C))"
              using B by (simp add: Comp_def Let_def set_addvars set_diff Var_def False)
            then show "in_equiv (A ;; CompA B C) (CompA B (A ;; C))"
              apply (simp add: False)
                by (simp add: in_equiv_eq)
          qed
        next
          case False
          assume [simp]: "out A \<notin> set (In C)"
          then show "in_equiv (CompA A (CompA B C)) (CompA B (CompA A C))"
            apply simp
          proof (cases "out B \<in> set (In C)")
            case True
            have [simp]: "out B \<in> set (In C)"
              by (simp add: True)
            have [simp]: "out A \<notin> set (In (B ;; C))"
              by (simp add: Comp_def Let_def set_addvars set_diff)
            then show "in_equiv (CompA A (CompA B C))  (CompA B C)" 
              by (simp add: Comp_assoc_new in_equiv_eq)
          next
            case False
            have [simp]: "out B \<notin> set (In C)"
              using False by simp
            then show "in_equiv (CompA A (CompA B C)) (CompA B C)" 
              by (simp add: in_equiv_eq)
          qed
        qed
  qed

    
fun In_Equiv :: "(('var, 'a) Dgr) list \<Rightarrow> (('var, 'a) Dgr) list \<Rightarrow> bool" where 
  "In_Equiv [] [] = True" |
  "In_Equiv (A # As) (B# Bs) = (in_equiv A B \<and> In_Equiv As Bs)" |
  "In_Equiv _ _ = False"
  
thm internal_def
  
thm fb_out_less_step_def
thm fb_less_step_def
  
thm CompA_commute_aux_b
thm CompA_commute_aux_a
 
lemma CompA_commute: 
  assumes [simp]: "io_diagram A"
    and [simp]: "io_diagram B"
    and [simp]: "io_diagram C"
    and [simp]: "length (Out A) = 1"
    and [simp]: "length (Out B) = 1"
    and [simp]: "out A \<notin> set (Out C)"
    and [simp]: "out B \<notin> set (Out C)"
    and [simp]: "out A \<noteq> out B"
    and [simp]: "deterministic (Trs A)"
    and [simp]: "deterministic (Trs B)"
    and A: "(out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A))"
  shows "in_equiv (CompA (CompA B A) (CompA B C)) (CompA (CompA A B) (CompA A C))"
    proof (cases "out A \<in> set (In B)")
      case True
      from this and A have [simp]: "out B \<notin> set (In A)"
        by simp
      then show ?thesis
        using True apply (subst CompA_commute_aux_a, simp_all)
          apply (rule in_equiv_eq)
         apply (metis BBB_a BaseOperationFeedbacklessVars.CompA_in BaseOperationFeedbacklessVars_axioms True assms(1) assms(2) assms(3) assms(4) assms(5) io_diagram_CompA)
          by simp
    next
      case False
      then have [simp]: "out A \<notin> set (In B)"
        by simp
      show ?thesis
      proof (cases "out B \<in> set (In A)")
        case True
        then show ?thesis
          thm CompA_commute_aux_a
          apply (subst CompA_commute_aux_a [of B A], simp_all)
          using assms(8) apply fastforce
          by (metis BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.CompA_in BaseOperationFeedbacklessVars_axioms assms(1) assms(2) assms(3) assms(4) assms(5) in_equiv_eq io_diagram_CompA)
      next
        case False
        then show ?thesis
          thm CompA_commute_aux_b
          by (subst CompA_commute_aux_b, simp_all)
      qed
    qed
  
  
lemma In_Equiv_CompA_twice: "(\<And> C . C \<in> set As \<Longrightarrow> io_diagram C \<and> out A \<notin> set (Out C) \<and> out B \<notin> set (Out C)) \<Longrightarrow> io_diagram A \<Longrightarrow> io_diagram B
    \<Longrightarrow> length (Out A) = 1 \<Longrightarrow> length (Out B) = 1 \<Longrightarrow> out A \<noteq> out B
    \<Longrightarrow> deterministic (Trs A) \<Longrightarrow> deterministic (Trs B)
    \<Longrightarrow> (out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A))
    \<Longrightarrow> In_Equiv (map (CompA (CompA B A)) (map (CompA B) As)) (map (CompA (CompA A B)) (map (CompA A) As))"
  apply (induction As, simp_all)
  by (rule CompA_commute, simp_all)
    
thm Type_OK_def
thm Deterministic_def
thm internal_def
thm fb_out_less_step_def

thm mem_get_other_out
  
thm mem_get_comp_out
  

thm comp_out_in
  

lemma map_diff: "(\<And> b . b \<in> set x \<Longrightarrow> b \<noteq> a \<Longrightarrow> f b \<noteq> f a) \<Longrightarrow> map f x \<ominus> [f a] = map f (x \<ominus> [a])"
  by (induction x, simp_all)


lemma In_Equiv_fb_out_less_step_commute: "Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> x \<in> internal As \<Longrightarrow>  y \<in> internal As  \<Longrightarrow> x \<noteq> y \<Longrightarrow> loop_free As
  \<Longrightarrow> In_Equiv (fb_out_less_step x (fb_out_less_step y As)) (fb_out_less_step y (fb_out_less_step x As))"
proof -
  assume "Deterministic As"
  assume "x \<noteq> y"
  assume loopfree: "loop_free As"

  assume [simp]: "Type_OK As"
    
  from this have [simp]: "\<And> A . A \<in> set As \<Longrightarrow> Out A = [out A]"
    using Type_OK_out by blast      
    
  define A where "A = get_comp_out x As"
  assume "x \<in> internal As"
  from this have A_As[simp]: "A \<in> set As" and out_A: "out A = x"
     by (simp_all add: A_def)

  define B where "B = get_comp_out y As"
  assume "y \<in> internal As"
  from this have B_As[simp]: "B \<in> set As" and out_B: "out B = y"
    by (simp_all add: B_def)
      
  have [simp]: " A \<noteq> B"
    using \<open>x \<noteq> y\<close> out_A out_B by auto
      
  from A_As obtain Bs Cs where As_A: "As = Bs @ A # Cs"
    by (meson split_list)

  from \<open>Type_OK As\<close> have "distinct As"
    using Type_OK_distinct by blast
  have As_minus_A: "As \<ominus> [A] = Bs @ Cs"
    apply (simp add: union_diff As_A)
    apply (subgoal_tac "Bs \<ominus> [A] = Bs")
     apply (subgoal_tac "Cs \<ominus> [A] = Cs")
      apply simp
     apply (metis AAA_c As_A  \<open>distinct As\<close> distinct.simps(2) distinct_append)
    by (metis AAA_c As_A UnCI \<open>distinct As\<close> append.simps(2) dist_perm distinct.simps(2) perm_tp set_append)
    
  have [simp]: "Out A = [out A]"
    using A_As Type_OK_out \<open>Type_OK As\<close> by blast
  have [simp]: "Out B = [out B]"
    using B_As Type_OK_out \<open>Type_OK As\<close> by blast
      
  from loopfree have "out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A)"
    apply (simp add: loop_free_def IO_Rel_def io_rel_def)
    apply (drule_tac x = "out A" in spec, safe)
    apply (subgoal_tac "(out A, out A) \<in> (UNION (set As) io_rel)\<^sup>+")
     apply simp
    apply (subst trancl_unfold_left)
    apply (simp add: relcomp_def OO_def)
    apply (rule_tac x = "out B" in exI, safe)
     apply (rule_tac x = A in bexI)
      apply (simp add: io_rel_def, simp_all)
      apply (rule r_into_rtrancl, simp)
    apply (rule_tac x = B in bexI)
     apply (simp add: io_rel_def)
    by simp
 
  have [simp]: "(fb_out_less_step x As) = map (CompA A) (As \<ominus> [A])"
    apply (simp add: fb_out_less_step_def A_def [THEN sym])
    apply (simp add: out_A[THEN sym])
    apply (subst mem_get_other_out, simp_all)
    by (simp add: fb_less_step_def)

  have [simp]: "(fb_out_less_step y As) =  map (CompA B) (As \<ominus> [B])"
    apply (simp add: fb_out_less_step_def B_def [THEN sym])
    apply (simp add: out_B[THEN sym])
    apply (subst mem_get_other_out, simp_all)
    by (simp add: fb_less_step_def As_A union_diff)
      
  thm mem_get_comp_out
    
  have y_out_CompA: "y = out (CompA A B)"
    by (metis A_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars.out_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> out_B)
      
  have x_out_CompA: "x = out (CompA B A)"
    by (metis B_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars.out_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> out_A)
    
  have [simp]: "Type_OK (map (CompA A) (As \<ominus> [A]))"
    by (metis A_As BaseOperationFeedbacklessVars.fb_out_less_step_def BaseOperationFeedbacklessVars.mem_get_other_out BaseOperationFeedbacklessVars_axioms Type_OK_fb_out_less_step_aux \<open>A \<equiv> get_comp_out x As\<close> \<open>Type_OK As\<close> \<open>fb_out_less_step x As = map (CompA A) (As \<ominus> [A])\<close> out_A)
    
  have [simp]: "Type_OK (map (CompA B) (As \<ominus> [B]))"
      by (metis B_As B_def BaseOperationFeedbacklessVars.fb_out_less_step_def BaseOperationFeedbacklessVars.mem_get_other_out BaseOperationFeedbacklessVars_axioms Type_OK_fb_out_less_step_aux \<open>Type_OK As\<close> \<open>fb_out_less_step y As = map (CompA B) (As \<ominus> [B])\<close> out_B)
    
      
  have [simp]: "get_comp_out y (map (CompA A) (As \<ominus> [A])) = CompA A B"
    apply (subgoal_tac "y = out (CompA A B)")
     apply (simp)
     apply (rule mem_get_comp_out)
      apply (simp_all add: set_diff image_def)
     apply (rule_tac x = B in bexI, simp_all)
    using \<open>A \<noteq> B\<close> apply blast
      using \<open>y = out (CompA A B)\<close> by blast
      
  have [simp]: "get_comp_out x (map (CompA B) (As \<ominus> [B])) = CompA B A"
    apply (subgoal_tac "x = out (CompA B A)")
     apply (simp)
     apply (rule mem_get_comp_out)
      apply (simp_all add: set_diff image_def)
     apply (rule_tac x = A in bexI, simp_all)
      by (rule x_out_CompA)
      
    thm mem_get_other_out
      
    have [simp]: "map (CompA A) (As \<ominus> [A]) \<ominus> [CompA A B] = map (CompA A) (As \<ominus> [A] \<ominus> [B])"
      apply (rule map_diff)
        by (metis A_As B_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms DiffE Type_OK_out \<open>Type_OK As\<close> list.simps(1) mem_get_comp_out set_diff)
      have [simp]: "map (CompA B) (As \<ominus> [B]) \<ominus> [CompA B A] = map (CompA B) (As \<ominus> [A] \<ominus> [B])"
        apply (subst map_diff)
         apply (metis A_As B_As BaseOperationFeedbacklessVars.BBB_a BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms DiffE Type_OK_out \<open>Type_OK As\<close> list.simps(1) mem_get_comp_out set_diff)
          by (simp add: diff_sym)

  have [simp]: "fb_out_less_step y (map (CompA A) (As \<ominus> [A])) = map (CompA (CompA A B)) (map (CompA A) (As \<ominus> [A] \<ominus> [B]))"
    apply (simp add: fb_out_less_step_def fb_less_step_def y_out_CompA)
    apply (subst mem_get_other_out, simp_all)
     apply (simp add: image_def set_diff)
     apply (rule_tac x = B in bexI, simp_all)
    using \<open>A \<noteq> B\<close> apply blast
    by (simp add: y_out_CompA[THEN sym])
      
  have [simp]: "fb_out_less_step x (map (CompA B) (As \<ominus> [B])) = map (CompA (CompA B A)) (map (CompA B) (As \<ominus> [A] \<ominus> [B]))"
    apply (simp add: fb_out_less_step_def fb_less_step_def x_out_CompA)
    apply (subst mem_get_other_out, simp_all)
     apply (simp add: image_def set_diff)
     apply (rule_tac x = A in bexI, simp_all)
    by (simp add: x_out_CompA[THEN sym])
      thm In_Equiv_CompA_twice
  show ?thesis
    apply (simp del: map_map)
    apply (rule In_Equiv_CompA_twice)
            apply simp_all
          apply (simp add: set_diff, safe)
    using BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> apply blast
           apply (metis  \<open>A \<equiv> get_comp_out x As\<close> \<open>Type_OK As\<close> mem_get_comp_out out_A )
          apply (metis \<open>B \<equiv> get_comp_out y As\<close> \<open>Type_OK As\<close>  mem_get_comp_out out_B )
         apply (meson A_As BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close>)
    using B_As BaseOperationFeedbacklessVars.Type_OK_def BaseOperationFeedbacklessVars_axioms \<open>Type_OK As\<close> apply blast
       apply (simp add: \<open>x \<noteq> y\<close> out_A out_B)
      using A_As Deterministic_def \<open>Deterministic As\<close> apply blast
      using B_As Deterministic_def \<open>Deterministic As\<close> apply blast
        using \<open>out A \<in> set (In B) \<Longrightarrow> out B \<notin> set (In A)\<close> by blast
   
    qed
      
lemma [simp]: "Type_OK As \<Longrightarrow> In_Equiv As As"
proof (induction As)
  case Nil
  then show ?case
    by simp
next
  case (Cons a As)
  then show ?case
    apply simp
    by (simp add: Type_OK_def in_equiv_eq)
qed
  
lemma fb_less_append: "\<And> As . fb_less (x @ y) As = fb_less y (fb_less x As)"
  proof (induction x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a x)
    then show ?case 
      by simp
  qed
    
  thm in_equiv_tran

    
lemma In_Equiv_trans: "\<And> Bs Cs . Type_OK Cs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> In_Equiv Bs Cs \<Longrightarrow> In_Equiv As Cs"
  proof (induction As)
    case Nil
    show ?case
      apply (case_tac Bs)
      using Nil.prems(3) apply blast
      using Nil.prems(2) by auto
  next
    case (Cons a As)
    show ?case
      apply (case_tac Bs)
      using Cons.prems(2) apply auto[1]
      apply (case_tac Cs, simp_all)
      using Cons.prems(3) In_Equiv.simps(3) apply blast
      apply safe
       apply (rule_tac B = aaa in in_equiv_tran)
      using Cons.prems(1) Type_OK_cons apply blast
        apply (metis Cons.prems(1) Cons.prems(2) Cons.prems(3) In_Equiv.simps(2) Type_OK_cons in_equiv_tran)
      using Cons.prems(1) Type_OK_cons in_equiv_eq apply blast
      using Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(3) In_Equiv.simps(2) Type_OK_cons by blast
    qed
      

  
lemma In_Equiv_exists: "\<And> Bs . In_Equiv As Bs \<Longrightarrow> A \<in> set As \<Longrightarrow> \<exists> B \<in> set Bs . in_equiv A B"
  proof (induction As)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a As)
    then show ?case
      by (case_tac Bs, simp_all, safe, simp)
  qed
       
lemma In_Equiv_Type_OK: "\<And>Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> Type_OK As"
proof (induction As)
  case Nil
  show ?case
    apply (case_tac Bs)
    using Nil.prems(1) apply blast
    using In_Equiv.simps(4) Nil.prems(2) by blast
next
  case (Cons a As)
  from Cons(3) obtain b Cs where [simp]: "Bs = b # Cs" and A: "in_equiv a b" and B[simp]: "In_Equiv As Cs"
    using In_Equiv.elims(2) by blast
      
  from A have [simp]: "length (Out a) = 1"
    apply (simp add: in_equiv_def)
    by (metis Cons.prems(1) One_nat_def Type_OK_cons \<open>Bs = b # Cs\<close>)
      
  from A have C: "Out a = Out b"
    by (simp add: in_equiv_def)
      
  show ?case
    apply (subst Type_OK_cons, safe)
    using Cons.prems(1) Type_OK_cons \<open>Bs = b # Cs\<close> \<open>in_equiv a b\<close> in_equiv_io_diagram apply blast
      apply simp
     apply (cut_tac A = aa and As = As and Bs = Cs in  In_Equiv_exists, simp_all)
     apply safe
     apply (simp add: C in_equiv_def)
    using Cons(2)
     apply (simp add: Type_OK_def)
      apply auto [1]
    using B Cons.IH Cons.prems(1) Type_OK_cons \<open>Bs = b # Cs\<close> by blast
qed
  
      
lemma In_Equiv_internal_aux: "Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> internal As \<subseteq> internal Bs"
  apply (simp add: internal_def, safe)
  apply (frule_tac A = A in In_Equiv_exists, blast)   
  apply (frule_tac A = B in In_Equiv_exists, blast)
  apply safe
  apply (rule_tac x = Ba in bexI, safe)
   apply (simp add: in_equiv_def out_def)
    using In_Equiv_exists in_equiv_def perm_set_eq by blast
    
    
lemma In_Equiv_sym: "\<And> Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> In_Equiv Bs As"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all)
next
  case (Cons a As)
  then show ?case
    apply (case_tac Bs, simp_all)
    apply (rule in_equiv_sym, simp_all)
    using Type_OK_cons by blast
qed

lemma In_Equiv_internal: "Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> internal As = internal Bs"
  apply (frule In_Equiv_Type_OK, blast)
  apply (frule In_Equiv_internal_aux, blast)
  apply (drule_tac As = Bs and Bs = As in In_Equiv_internal_aux)
  by (rule In_Equiv_sym, simp_all)

lemma in_equiv_CompA: "in_equiv A A' \<Longrightarrow> in_equiv B B' \<Longrightarrow> io_diagram A' \<Longrightarrow> io_diagram B' \<Longrightarrow> in_equiv (CompA A B) (CompA A' B')"
  apply (simp add: CompA_def)
    apply (case_tac "out A \<in> set (In B)", simp_all, safe)
    apply (rule in_equiv_Comp, simp_all)
    apply (subst (asm) in_equiv_def) 
   apply (subst (asm) in_equiv_def, safe)
   apply (simp add: out_def)
  using perm_set_eq apply blast
    apply (subst (asm) in_equiv_def) 
   apply (subst (asm) in_equiv_def, safe)
   apply (simp add: out_def)
  using perm_set_eq by blast
    
lemma In_Equiv_fb_less_step_cong: "\<And> Bs . Type_OK Bs \<Longrightarrow> in_equiv A B \<Longrightarrow> io_diagram B \<Longrightarrow> In_Equiv As Bs
    \<Longrightarrow> In_Equiv (fb_less_step A As) (fb_less_step B Bs)"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all add: fb_less_step_def)
next
  case (Cons b As)
  then show ?case
    apply (case_tac Bs, simp_all)
    apply (simp add: fb_less_step_def)
    apply (rule in_equiv_CompA)
       apply simp_all
    using Type_OK_cons by blast
qed
  
lemma In_Equiv_append: "\<And> As' . In_Equiv As As' \<Longrightarrow> In_Equiv Bs Bs' \<Longrightarrow> In_Equiv (As @ Bs) (As' @ Bs')"   
proof (induction As)
  case Nil
  then show ?case
    apply (case_tac As')
    by simp_all
next
  case (Cons a As)
  then show ?case
    by (case_tac As', simp_all)
qed
  
lemma In_Equiv_split: "\<And> Bs . In_Equiv As Bs \<Longrightarrow> A \<in> set As 
    \<Longrightarrow> \<exists> B As' As'' Bs' Bs'' . As = As' @ A # As'' \<and> Bs = Bs' @ B # Bs'' \<and> in_equiv A B \<and> In_Equiv As' Bs' \<and> In_Equiv As'' Bs''"
proof (induction As)
  case Nil
  then show ?case
    by simp
next
  case (Cons a As)
  then show ?case
  proof (cases "a = A")
    case True
    from this and Cons show ?thesis
    apply (simp_all, safe)
      apply (case_tac Bs, simp_all)
     apply (rule_tac x = aa in exI)
     apply (rule_tac x = "[]" in exI)
      apply (rule_tac x = As in exI, simp)
     apply (rule_tac x = "[]" in exI)
     by (rule_tac x = list in exI, simp)      
  next
    case False
    obtain b Ba where [simp]: "Bs = b # Ba"
      using Cons.prems(1) In_Equiv.elims(2) by blast
    
    have "A \<in> set As"
      using Cons.prems(2) False by auto
        
    have "In_Equiv As Ba"
      using Cons.prems(1) \<open>Bs = b # Ba\<close> by auto
        
    have [simp]: "in_equiv a b"
      using Cons.prems(1) In_Equiv.simps(2) \<open>Bs = b # Ba\<close> by blast
        
    obtain B As' As'' Bs' Bs'' where [simp]: "As = As' @ A # As''" and [simp]: "Ba = Bs' @ B # Bs''" 
        and [simp]: "in_equiv A B" and [simp]: "In_Equiv As' Bs'" and [simp]: "In_Equiv As'' Bs''"
      using Cons.IH \<open>A \<in> set As\<close> \<open>In_Equiv As Ba\<close> by blast
        
    show ?thesis
      apply simp
      apply (rule_tac x = B in exI, simp)
      apply (rule_tac x = "a # As'" in exI, simp)
      by (rule_tac x = "b # Bs'" in exI, simp)
  qed  
qed

    
lemma In_Equiv_fb_out_less_step_cong: 
  assumes [simp]: "Type_OK Bs"
    and "In_Equiv As Bs"
    and internal: "a \<in> internal As"
    shows "In_Equiv (fb_out_less_step a As) (fb_out_less_step a Bs)"
proof -
  have [simp]: "Type_OK As"
    using In_Equiv_Type_OK assms(1) assms(2) by blast

  obtain A where "A \<in> set As" and "out A = a"
    using internal by (subst (asm) internal_Type_OK_simp, simp_all, blast)
      
  have [simp]: "get_comp_out a As = A"
    using \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_comp_out by blast
      
  have [simp]: "get_other_out a As = As \<ominus> [A]"
    using \<open>A \<in> set As\<close> \<open>Type_OK As\<close> \<open>out A = a\<close> mem_get_other_out by blast
      
  obtain B As' As'' Bs' Bs'' where As_split: "As = As' @ A # As''" and Bs_split: "Bs = Bs' @ B # Bs''" and [simp]: "in_equiv A B" 
      and [simp]: "In_Equiv As' Bs'" and [simp]: "In_Equiv As'' Bs''"
    using In_Equiv_split \<open>A \<in> set As\<close> assms(2) by blast
      
  have "out B = a"
    by (metis \<open>in_equiv A B\<close> \<open>out A = a\<close> in_equiv_def out_def)
      
  have "B \<in> set Bs"
    by (simp add: \<open>Bs = Bs' @ B # Bs''\<close>)
      
  have [simp]: "get_comp_out a Bs = B"
    using \<open>B \<in> set Bs\<close> \<open>Type_OK Bs\<close> \<open>out B = a\<close> mem_get_comp_out by blast

  have [simp]: "get_other_out a Bs = Bs \<ominus> [B]"
    using \<open>B \<in> set Bs\<close> \<open>Type_OK Bs\<close> \<open>out B = a\<close> mem_get_other_out by blast
      
  have "distinct As"
    by (simp add: Type_OK_distinct )

  have [simp]: "As \<ominus> [A] = As' @ As''"
    apply (simp add: As_split union_diff)
    by (metis AAA_c As_split \<open>distinct As\<close> disjoint_insert(2) distinct.simps(2) distinct_append list.simps(15))
      
  have "distinct Bs"
    by (simp add: Type_OK_distinct)

  have Bs_diff: "Bs \<ominus> [B] = Bs' @ Bs''"
    apply (simp add: Bs_split union_diff)
    by (metis AAA_c Bs_split \<open>distinct Bs\<close> disjoint_insert(2) distinct.simps(2) distinct_append list.simps(15))
      

  show ?thesis
    apply (simp add: fb_out_less_step_def)
    apply (rule In_Equiv_fb_less_step_cong)
       apply (metis Diff_iff Type_OK_def \<open>get_other_out a Bs = Bs \<ominus> [B]\<close> assms(1) concat_map_Out_get_other_out distinct_diff set_diff)
      apply simp
    using Type_OK_def \<open>B \<in> set Bs\<close> assms(1) apply blast
    by (simp add: Bs_diff In_Equiv_append)
qed
 
lemma In_Equiv_IO_Rel: "\<And> Bs . In_Equiv As Bs \<Longrightarrow> IO_Rel Bs = IO_Rel As"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all)
next
  case (Cons a As)
    
  obtain B Bs' where [simp]: "Bs = B # Bs'"
    using In_Equiv.elims(2) local.Cons(2) by blast
  have [simp]: "(\<Union>x\<in>set Bs'. io_rel x) = (\<Union>x\<in>set As . io_rel x)"
    by (metis Cons.IH IO_Rel_def In_Equiv.simps(2) \<open>Bs = B # Bs'\<close> local.Cons(2) set_map)
      
  have "in_equiv a B"
    using Cons.prems by auto

  from this have [simp]: "io_rel a = io_rel B"
    by (metis in_equiv_def io_rel_def perm_set_eq)
     
  then show ?case
      by (simp add: IO_Rel_def)
qed
  
      
lemma In_Equiv_loop_free: "In_Equiv As Bs \<Longrightarrow> loop_free Bs \<Longrightarrow> loop_free As"
  apply (simp add: loop_free_def)
  by (subgoal_tac "IO_Rel Bs = IO_Rel As", simp_all add: In_Equiv_IO_Rel)
    
lemma loop_free_fb_out_less_step_internal: 
  assumes [simp]: "loop_free As"
    and [simp]: "Type_OK As"
    and "a \<in> internal As"
    shows "loop_free (fb_out_less_step a As)"
proof -
  obtain A where [simp]: "A \<in> set As" and [simp]: "out A = a"
    using assms(3) by (simp add: internal_Type_OK_simp, blast)
  show ?thesis
    by (rule_tac A = A in loop_free_fb_out_less_step, simp_all)
qed

lemma loop_free_fb_less_internal: 
  "\<And> As . loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x \<Longrightarrow> loop_free (fb_less x As)"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply (simp)
    apply (rule Cons(1))
       apply (rule loop_free_fb_out_less_step_internal)
         apply simp_all
    using Type_OK_fb_out_less_step_new apply blast
    by (metis Diff_empty internal_fb_out_less_step subset_Diff_insert)
qed

  
      
     
lemma In_Equiv_fb_less_cong: "\<And> As Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow>  distinct x \<Longrightarrow> loop_free Bs \<Longrightarrow> In_Equiv (fb_less x As) (fb_less x Bs)"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  have [simp]: "a \<in> internal Bs"
    by (metis Cons.prems(1) Cons.prems(2) Cons.prems(3) In_Equiv_internal list.set_intros(1) subsetCE)
  have [simp]: "Type_OK (fb_out_less_step a Bs)"
    using Cons.prems(1) Cons.prems(5) Type_OK_fb_out_less_step_new \<open>a \<in> internal Bs\<close> by blast
  have "Type_OK As"
    using Cons.prems(1) Cons.prems(2) In_Equiv_Type_OK by blast
  show ?case
    apply simp
    apply (rule Cons(1))
        apply simp_all
       apply (rule In_Equiv_fb_out_less_step_cong)
         apply (simp_all add: Cons)
    using Cons.prems(3) apply auto[1]
      apply (subst internal_fb_out_less_step)
    using Cons.prems(2) Cons.prems(5) In_Equiv_loop_free apply blast
        apply (simp add: \<open>Type_OK As\<close>)
    using Cons.prems(3) apply auto[1]
    using Cons.prems(3) Cons.prems(4) apply auto[1]
    using Cons.prems(4) apply auto [1]
    apply (rule loop_free_fb_out_less_step_internal)
    by (simp_all add: Cons)
qed
  
      
      
thm Type_OK_fb_out_less_step_new

thm Type_OK_fb_less
  
lemma Type_OK_fb_less_delete: "\<And> As . Type_OK As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x \<Longrightarrow> loop_free As \<Longrightarrow> Type_OK (fb_less x As)"
  by (rule Type_OK_fb_less, simp_all)

  
  
thm Deterministic_fb_out_less_step
  
thm internal_fb_out_less_step
  
lemma internal_fb_less: 
  "\<And> As . loop_free As \<Longrightarrow> Type_OK As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x \<Longrightarrow> internal (fb_less x As) = internal As - set x"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply simp
    apply (subst Cons(1))
        apply simp_all
    using loop_free_fb_out_less_step_internal apply blast
    using Type_OK_fb_out_less_step_new apply blast
     apply (metis Diff_empty internal_fb_out_less_step subset_Diff_insert)
    using internal_fb_out_less_step by auto    
qed
  

thm  Deterministic_fb_out_less_step
  
  
lemma Deterministic_fb_out_less_step_internal:
  assumes [simp]: "Type_OK As"
    and "Deterministic As"
    and internal: "a \<in> internal As"
  shows "Deterministic (fb_out_less_step a As)"
proof -
  obtain A where "A \<in> set As" and "out A = a"
    using internal by (simp add: internal_Type_OK_simp, blast)
  show ?thesis
    using Deterministic_fb_out_less_step \<open>A \<in> set As\<close> \<open>out A = a\<close> assms(1) assms(2) by blast
qed
  
lemma Deterministic_fb_less_internal: "\<And> As . Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow> distinct x 
\<Longrightarrow> loop_free As \<Longrightarrow> Deterministic (fb_less x As)"
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply simp
    apply (rule Cons(1), simp_all)
    using Type_OK_fb_out_less_step_new apply blast
    using Deterministic_fb_out_less_step_internal apply blast
      apply (subst internal_fb_out_less_step, simp_all, blast)
    using loop_free_fb_out_less_step_internal by blast
qed
  
    
lemma In_Equiv_fb_less_Cons: "\<And> As . Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> a \<in> internal As 
\<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow>  distinct (a # x)
  \<Longrightarrow> In_Equiv (fb_less (a # x) As) (fb_less (x @ [a]) As)"
proof (induction x)
  case Nil
  have [simp]:"Type_OK (fb_out_less_step a As)"
    using Nil.prems(1) Nil.prems(3) Nil.prems(4) Type_OK_fb_out_less_step_new by blast
  from Nil show ?case
    by simp_all
next
  case (Cons b x)
  have [simp]: "Type_OK (fb_out_less_step b As)"
    by (metis Cons.prems(1) Cons.prems(5) Type_OK_fb_out_less_step_new insert_subset list.simps(15))
  have [simp]: "Deterministic (fb_out_less_step b As)"
    apply (rule Deterministic_fb_out_less_step_internal)
      apply (simp_all add: Cons)
    using Cons.prems(5) by auto
  have [simp]: " Type_OK (fb_out_less_step a (fb_less x (fb_out_less_step b As)))"
    apply (rule Type_OK_fb_out_less_step_new, simp_all)
     apply (rule Type_OK_fb_less, simp_all)
     apply (meson Cons.prems(1) Cons.prems(3) Cons.prems(5) list.set_intros(1) loop_free_fb_out_less_step_internal subset_iff)
    using Cons.prems(6) apply auto[1]
     apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(5) Cons.prems(6) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)
    by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) DiffI distinct.simps(2) fb_less.simps(2) internal_fb_less)
  have [simp]: "Type_OK (fb_out_less_step a (fb_out_less_step b As))"
    apply (rule Type_OK_fb_out_less_step_new, simp_all)
      by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) distinct_length_2_or_more insert_Diff insert_iff internal_fb_out_less_step list.set_intros(1) subset_eq)
  have [simp]: "set x \<subseteq> internal (fb_out_less_step b (fb_out_less_step a As))"
  proof -
    have f1: "\<And>v. v \<in> insert b (set x) \<or> set x \<subseteq> internal As - {v}"
      by (metis (no_types) Cons.prems(5) Diff_empty insert_subset list.simps(15) subset_Diff_insert)
    have "b \<in> internal As - {a}"
      by (metis (no_types) Cons.prems(5) Cons.prems(6) Diff_empty distinct.simps(2) insert_subset list.simps(15) subset_Diff_insert)
    then show ?thesis
      using f1 by (metis (no_types) Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(6) Diff_empty Type_OK_fb_out_less_step_new distinct.simps(2) internal_fb_out_less_step list.simps(15) loop_free_fb_out_less_step_internal subset_Diff_insert)
  qed
  have [simp]: "loop_free (fb_out_less_step a (fb_out_less_step b As))"
    by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Type_OK_fb_out_less_step_new distinct_length_2_or_more insert_Diff insert_iff insert_subset internal_fb_out_less_step list.simps(15) loop_free_fb_out_less_step_internal)
  have [simp]: "In_Equiv (fb_less x (fb_out_less_step a (fb_out_less_step b As))) (fb_out_less_step a (fb_less x (fb_out_less_step b As)))"
    apply (cut_tac Cons(1)[of "fb_out_less_step b As"])
          apply (simp add: fb_less_append)
         apply (simp_all add: Cons)
      
       apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(5) insert_subset list.simps(15) loop_free_fb_out_less_step_internal)
      apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) distinct_length_2_or_more insert_Diff insert_iff internal_fb_out_less_step list.set_intros(1) subsetCE)
     apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(5) Cons.prems(6) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)
    using Cons.prems(6) by auto      
  show ?case
    apply (simp add: fb_less_append)
    apply (rule_tac Bs = "(fb_less x (fb_out_less_step a (fb_out_less_step b As)))" in In_Equiv_trans)
      apply simp
      apply (rule In_Equiv_fb_less_cong)
         apply simp_all
        apply (rule In_Equiv_fb_out_less_step_commute)
             apply (simp_all add: Cons)
    using Cons.prems(5) apply auto[1]
    using Cons.prems(6) apply auto[1]
    using Cons.prems(6) by auto[1]
qed
 
    
theorem In_Equiv_fb_less: "\<And> y As . Type_OK As \<Longrightarrow> Deterministic As \<Longrightarrow> loop_free As \<Longrightarrow> set x \<subseteq> internal As \<Longrightarrow>  distinct x \<Longrightarrow> perm x y
  \<Longrightarrow> In_Equiv (fb_less x As) (fb_less y As)"
  
proof (induction x)
  case Nil
  then show ?case
    by simp_all
next
  case (Cons a x)
  obtain y' y'' where A: "y = y' @ a # y''" and [simp]: "perm x (y' @ y'')"
    by (meson Cons.prems(6) split_perm)
      
  have [simp]: "Type_OK (fb_out_less_step a As)"
    by (meson Cons.prems(1) Cons.prems(4) Type_OK_fb_out_less_step_new list.set_intros(1) subset_eq)
      
  have [simp]: "Deterministic (fb_out_less_step a As)"
    by (metis Cons.prems(1) Cons.prems(2) Cons.prems(4) Deterministic_fb_out_less_step_internal insert_subset list.simps(15))
      
  have [simp]: "loop_free (fb_out_less_step a As)"
    by (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) insert_subset list.simps(15) loop_free_fb_out_less_step_internal)
      
  have [simp]: "Type_OK (fb_out_less_step a (fb_less y' As))"
    apply (subgoal_tac "fb_out_less_step a (fb_less y' As) = fb_less (y' @ [a]) As")
     apply simp
     apply (rule Type_OK_fb_less, simp_all add: Cons)
     apply (metis Cons.prems(5) UnI1 \<open>perm x (y' @ y'')\<close> dist_perm distinct.simps(2) distinct_append perm_set_eq set_append)
    using Cons.prems(4) \<open>perm x (y' @ y'')\<close>
      apply (cut_tac perm_set_eq [of x "y' @ y''"], simp_all)
    by (simp add: fb_less_append)
      

  have [simp]: "Type_OK (fb_less y'' (fb_out_less_step a (fb_less y' As)))"
    apply (subgoal_tac "fb_less y'' (fb_out_less_step a (fb_less y' As)) = fb_less (y' @ a # y'') As")
      apply simp
     apply (rule Type_OK_fb_less, simp_all add: Cons)
     apply (metis A Cons.prems(5) Cons.prems(6) \<open>perm x (y' @ y'')\<close> dist_perm distinct.simps(2) distinct_append not_distinct_conv_prefix)
      apply (metis (no_types, lifting) Cons.prems(4) ListProp.perm_set_eq \<open>x <~~> y' @ y''\<close> insert_subset le_sup_iff list.simps(15) set_append)
    by (simp add: fb_less_append)
      
  have B: "distinct y \<and> set y \<subseteq> internal As"
    using Cons.prems(4) Cons.prems(5) Cons.prems(6) dist_perm perm_set_eq by blast
      
  have [simp]: "set y'' \<subseteq> internal (fb_less y' (fb_out_less_step a As))"
    apply (subst internal_fb_less, simp_all)
      apply (subst internal_fb_out_less_step, simp_all add: Cons)
    using Cons.prems(4) apply auto[1]
    using A B apply (simp add: subset_Diff_insert)
    using A Cons.prems(5) Cons.prems(6) dist_perm distinct_append apply blast
      apply (subst internal_fb_out_less_step, simp_all add: Cons)
    using Cons.prems(4) apply auto[1]
    using A B by auto
      
  have [simp]: "loop_free (fb_out_less_step a (fb_less y' As))"
  proof -
    have f1: "distinct y"
      using Cons.prems(5) Cons.prems(6) dist_perm by blast
    have "set y \<subseteq> internal As"
      using Cons.prems(4) Cons.prems(6) perm_set_eq by blast
    then have "loop_free (fb_less (y' @ [a]) As)"
      using f1 by (simp add: A Cons.prems(1) Cons.prems(3) loop_free_fb_less_internal)
    then show "loop_free (fb_out_less_step a (fb_less y' As))"
      by (simp add: fb_less_append)
  qed
      
  show ?case
    apply (simp add: A fb_less_append)
    apply (rule_tac Bs = "fb_less y'' (fb_less y' (fb_out_less_step a As))" in In_Equiv_trans, simp)
     apply (simp add: fb_less_append[THEN sym])
     apply (rule Cons(1), simp_all)
      apply (metis Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) Diff_empty distinct.simps(2) insert_subset internal_fb_out_less_step list.simps(15) subset_Diff_insert)
    using Cons.prems(5) apply auto[1]
    apply (rule In_Equiv_fb_less_cong, simp_all)
      apply (cut_tac In_Equiv_fb_less_Cons, simp add: fb_less_append)
            apply (simp_all add: Cons)
    using Cons.prems(4) apply auto[1]
      using A B apply auto[1]
      apply (metis Cons.prems(5) UnI1 \<open>perm x (y' @ y'')\<close> dist_perm distinct.simps(2) distinct_append perm_set_eq set_append)
    by (metis A Cons.prems(5) Cons.prems(6) dist_perm distinct.simps(2) distinct_append)
qed
 
lemma [simp]: "in_equiv \<box> \<box>"
  apply (simp add: in_equiv_def)
  by (simp add: switch.simps(1))
    
  
lemma in_equiv_Parallel_list: "\<And> Bs . Type_OK Bs \<Longrightarrow> In_Equiv As Bs \<Longrightarrow> in_equiv (Parallel_list As) (Parallel_list Bs)"
proof (induction As)
  case Nil
  then show ?case
    by (case_tac Bs, simp_all)
next
  case (Cons a As)
    
  obtain B Bs' where A[simp]: "Bs = B # Bs'"
    using In_Equiv.elims(2) local.Cons(3) by blast
    
  have B: "in_equiv (Parallel_list As) (Parallel_list Bs')"
    apply (rule Cons(1))
    using Cons.prems by auto

  show ?case
    apply simp
    by (metis Cons.prems(1) Cons.prems(2) In_Equiv.simps(2) Type_OK_cons A
        B in_equiv_Parallel io_diagram_parallel_list)        
qed
  
  
thm FB_fb_less
  
lemma [simp]: "io_diagram A \<Longrightarrow> distinct (VarFB A)"
  by (simp add: VarFB_def)
    
lemma [simp]: "io_diagram A \<Longrightarrow> distinct (InFB A)"
  by (simp add: InFB_def)
    
theorem fb_perm_eq_Parallel_list:
  assumes [simp]: "Type_OK As"
    and [simp]: "Deterministic As"
    and [simp]: "loop_free As"
    shows "fb_perm_eq (Parallel_list As)"
proof (simp add: fb_perm_eq_def, safe)
  fix x
  assume perm [simp]: "perm x (VarFB (Parallel_list As))"
    
  have length: "length(VarFB (Parallel_list As)) = length x"
    by (metis Permutation.perm_length perm)

  define y where "y = VarFB (Parallel_list As)"
      
  define X where "X = Parallel_list (fb_less x As)"
  define Y where "Y = Parallel_list (fb_less y As)"

      
  have A: "(fb ^^ length x) ([x @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] oo Trs (Parallel_list As) 
      oo [Out (Parallel_list As) \<leadsto> x @ OutFB (Parallel_list As)]) 
      = [InFB (Parallel_list As) \<leadsto> In X] oo Trs X"
    and perm_x: "perm (InFB (Parallel_list As)) (In X)"
    apply (subst FB_fb_less, simp_all add: X_def perm_sym)
    by (subst FB_fb_less, simp_all add: X_def perm_sym)
      
  have B: "(fb ^^ length (VarFB (Parallel_list As))) ([VarFB (Parallel_list As) @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] 
      oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> VarFB (Parallel_list As) @ OutFB (Parallel_list As)]) 
      = [InFB (Parallel_list As) \<leadsto> In Y] oo Trs Y"
    and perm_y: "perm (InFB (Parallel_list As)) (In Y)"
    apply (subst FB_fb_less, simp_all add: Y_def y_def)
    by (subst FB_fb_less, simp_all add: Y_def y_def)
      
  thm In_Equiv_fb_less
    
  have [simp]: "set x \<subseteq> internal As"
    by (simp add: internal_VarFB)

  have perm[simp]: "perm (VarFB (Parallel_list As)) x"
    by (simp add: perm_sym)

  have "io_diagram (Parallel_list As)"
    using io_diagram_parallel_list assms(1) by blast
      
  from this have "distinct (VarFB (Parallel_list As))"
    by simp
      
  from this have [simp]: "distinct x"
    using perm dist_perm by blast
    

  have [simp]: "In_Equiv (fb_less x As) (fb_less y As)"
    by (rule In_Equiv_fb_less, simp_all add: y_def)
      
      
  have [simp]: "Type_OK (fb_less y As)"
    using Type_OK_fb_less \<open>distinct (VarFB (Parallel_list As))\<close> \<open>set x \<subseteq> internal As\<close> \<open>y \<equiv> VarFB (Parallel_list As)\<close> assms(1) assms(3) perm perm_set_eq by blast
      
  have [simp]: "io_diagram Y"
    by (simp add: Y_def io_diagram_parallel_list)
      
  have [simp]: "io_diagram (Parallel_list As)"
    by (simp add: io_diagram_parallel_list)

              
  have "in_equiv (Parallel_list (fb_less x As)) (Parallel_list (fb_less y As))"
    by (subst in_equiv_Parallel_list, simp_all)
     
      
  from this have "perm (In X) (In Y)" and "Trs X = [In X \<leadsto> In Y] oo Trs Y" and "Out X = Out Y"
    by (simp_all add: in_equiv_def X_def [THEN sym] Y_def [THEN sym])
          
      
  from this have "[InFB (Parallel_list As) \<leadsto> In X] oo Trs X = [InFB (Parallel_list As) \<leadsto> In X] oo ([In X \<leadsto> In Y] oo Trs Y)"
    by simp
  also have "... =  ([InFB (Parallel_list As) \<leadsto> In X] oo [In X \<leadsto> In Y]) oo Trs Y"
    by (simp add: comp_assoc)
  also have "... = [InFB (Parallel_list As) \<leadsto>  In Y] oo Trs Y"
    apply (subst switch_comp, simp_all add: perm_x)
    by (simp add: \<open>perm (In X) (In Y)\<close>)
  
  finally show  "(fb ^^ length (VarFB (Parallel_list As)))
          ([VarFB (Parallel_list As) @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] 
          oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> VarFB (Parallel_list As) @ OutFB (Parallel_list As)]) =
         (fb ^^ length (VarFB (Parallel_list As))) ([x @ InFB (Parallel_list As) \<leadsto> In (Parallel_list As)] 
          oo Trs (Parallel_list As) oo [Out (Parallel_list As) \<leadsto> x @ OutFB (Parallel_list As)])"
    apply (simp add: B)
    by (simp add: length A)
qed
  

theorem FeedbackSerial_Feedbackless: "io_diagram A \<Longrightarrow> io_diagram B \<Longrightarrow> set (In A) \<inter> set (In B) = {} (*required*)
      \<Longrightarrow> set (Out A) \<inter> set (Out B) = {} \<Longrightarrow> fb_perm_eq (A ||| B) \<Longrightarrow> FB (A ||| B) = FB (FB (A) ;; FB (B))"
proof -
  assume [simp]: "io_diagram A"
          assume [simp]: "io_diagram B"
          assume [simp]: "set (In A) \<inter> set (In B) = {}"
          assume [simp]: "set (Out A) \<inter> set (Out B) = {}"
            
          assume fb_perm_eq: "fb_perm_eq (A ||| B)"
            

          define I where "I \<equiv> (In (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B))"
            
          define O' where "O' \<equiv> (Out (A ||| B)) \<ominus> (Var (A ||| B) (A ||| B))"

          define IA' where "IA' \<equiv> In A \<ominus> Out A \<ominus> Out B"
          define IB' where "IB' \<equiv> In B \<ominus> Out A \<ominus> Out B"

          define IA'' where "IA'' \<equiv> In A \<ominus> Out A"
          define IB'' where "IB'' \<equiv> In B \<ominus> Out B"

          define OA' where "OA' \<equiv> Out A \<ominus> In A \<ominus> In B"
          define OB' where "OB' \<equiv> Out B \<ominus> In A \<ominus> In B"
          
          define OA'' where "OA'' \<equiv> Out A \<ominus> In A"
          define OB'' where "OB'' \<equiv> Out B \<ominus> In B"

          have [simp]: "TI (Trs A) = TVs (In A)"
            apply (subgoal_tac "io_diagram A")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "TI (Trs B) = TVs (In B)"
            apply (subgoal_tac "io_diagram B")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "TO (Trs A) = TVs (Out A)"
            apply (subgoal_tac "io_diagram A")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "TO (Trs B) = TVs (Out B)"
            apply (subgoal_tac "io_diagram B")
            apply (unfold io_diagram_def)[1]
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
            by (simp add: O'_def)

          have [simp]: "distinct I"
            by (simp add: I_def Parallel_indep Var_def)
          

          have [simp]: "distinct IA'"
            by (simp add: IA'_def)

          have [simp]: "distinct IB'"
            by (simp add: IB'_def)

          have [simp]: "TI (Trs (A ||| B)) = TVs (In (A ||| B))"
            by (simp add: Parallel_indep)

          have [simp]: "TO (Trs (A ||| B)) = TVs (Out (A ||| B))"
            by (simp add: Parallel_indep)
          
          have [simp]: "distinct (Out A)"
            apply (subgoal_tac "io_diagram A")
            apply (unfold io_diagram_def)[1]
            by simp_all
 
          have [simp]: "distinct (Out B)"
            apply (subgoal_tac "io_diagram B")
            apply (unfold io_diagram_def)[1]
            by simp_all

          have [simp]: "distinct (Var A A)"
            by (simp add: Var_def )

          have [simp]: "distinct (Var B B)"
            by (simp add: Var_def )

          have [simp]: "distinct (Var A B)"
            by (simp add: Var_def )

          have [simp]: "distinct (Var B A)"
            by (simp add: Var_def )

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
            by (simp add: OA'_def )

          have [simp]: "distinct OB'" 
            by (simp add: OB'_def )

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
            by (simp add: I_simp perm_mset union_lcomm)

          have [simp]: "perm (Var B B @ Var B A @ OB' @ Var A B @ OA') (Var A B @ OA' @ Var B B @ Var B A @ OB')"
            by (simp add: perm_mset)

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
            by (simp add: I_simp perm_mset)

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
                apply (simp add: IA''_def)
                  using perm_diff_left_inter perm_sym by blast
 
              have B: "((In A \<ominus> Out A) \<otimes> Out B) = (In A \<otimes> Out B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp

              have C: "perm (In A \<otimes> Out B) (Out B \<otimes> In A)"
                apply (simp add:  perm_mset)
                using \<open>distinct (Out B)\<close> \<open>io_diagram A\<close> perm_mset perm_switch_aux_d io_diagram_def
                  by metis

              have D: "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B))"
                by (simp add: B C perm_union_left)

              have E: "perm ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B)) (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B))"
                by (simp only: D perm_sym)

              show "perm (Var B A @ IA') IA''"
                apply (simp add: Var_def IA'_def)
                apply (subgoal_tac "perm ((Out B \<otimes> In A) @ (In A \<ominus> Out A \<ominus> Out B)) (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B))")
                 apply (subgoal_tac "perm (((In A \<ominus> Out A) \<otimes> Out B) @ (In A \<ominus> Out A \<ominus> Out B)) IA''")
                  using perm_trans apply blast
                by (simp_all only: E A )
            qed

          have [simp]: "perm (Var A B @ OA') OA''"
            proof -
              have A: "perm (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B)) OA''"
                apply (simp add: OA''_def)
                  using perm_diff_left_inter perm_sym by blast

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
            apply (metis perm_mset perm_tp)
            by simp

          have [simp]: "perm (Out A) (Var A A @ OA'')"
            apply (simp add: OA''_def Var_def )
            using \<open>io_diagram A\<close> perm_switch_aux_c perm_sym io_diagram_def by blast

          have [simp]: "distinct OA''"
            by (simp add: OA''_def)

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
                apply (simp add: IB''_def)
                  using perm_diff_left_inter perm_sym by blast

              have B: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) IB''"
                apply (subst diff_sym)
                by (simp add: A)
 
              have C: "((In B \<ominus> Out B) \<otimes> Out A) = (In B \<otimes> Out A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (Out A) \<inter> set (Out B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp

              have D: "perm (In B \<otimes> Out A) (Out A \<otimes> In B)"
                apply (simp add: perm_mset)
                apply (subgoal_tac "distinct (Var A B)")
                apply (subgoal_tac "io_diagram B")
                apply (simp only: Var_def io_diagram_def)
                apply (metis Int_commute distinct_inter set_eq_iff_mset_eq_distinct set_inter)
                by simp_all

              have E: "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B))"
                by (simp add: B C D perm_union_left)

              have F: "perm ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B)) (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B))"
                by (simp only: E perm_sym)

              show "perm (Var A B @ IB') IB''"
                apply (simp add: Var_def IB'_def)
                apply (subgoal_tac "perm ((Out A \<otimes> In B) @ (In B \<ominus> Out A \<ominus> Out B)) (((In B \<ominus> Out B) \<otimes> Out A) @(In B \<ominus> Out A \<ominus> Out B))")
                 apply (subgoal_tac "perm (((In B \<ominus> Out B) \<otimes> Out A) @ (In B \<ominus> Out A \<ominus> Out B)) IB''")
                  using perm_trans apply blast
                by (simp_all only: F B)
            qed

         have [simp]: "perm (Out B) (Var B B @ OB'')"
           apply (simp add: OB''_def Var_def)
             by (metis diff_inter_left mset_inter_diff perm_mset union_code)

         have [simp]: "perm (OA'' @ IB') (Var A B @ OA' @ IB')"
            by (metis perm_union_left \<open>perm (Var A B @ OA') OA''\<close> append_assoc perm_sym)

         have [simp]: "perm (OA'' @ IB') (OA' @ Var A B @ IB')"
            by (metis perm_union_left \<open>perm (OA' @ Var A B) OA''\<close> append_assoc perm_sym)

         have [simp]: "perm (Var B A @ OB') OB''"
            proof -
              have A: "perm (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In B \<ominus> In A)) OB''"
                apply (simp add: OB''_def )
                  using perm_diff_left_inter perm_sym by blast
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
                by (metis OA''_def Var_def \<open>perm (Out A) (Var A A @ OA'')\<close>)
              have B: "perm (Out A \<ominus> In A) (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                using perm_diff_left_inter by blast
              have C: "((Out A \<ominus> In A) \<otimes> In B) = (Out A \<otimes> In B)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have D: "perm (Out A \<ominus> In A) ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out A \<ominus> In A) (((Out A \<ominus> In A) \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                 apply (subgoal_tac "((Out A \<ominus> In A) \<otimes> In B) = (Out A \<otimes> In B)")
                  apply simp
                apply (simp only: C)
                by (simp only: B)
              
              have E: "perm (Out A)  ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out A) ((Out A \<otimes> In A) @ (Out A \<ominus> In A))")
                 apply (subgoal_tac "perm (Out A \<ominus> In A) ((Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                  apply (metis perm_mset union_code)
                apply (simp only: D)
                by (simp only: A)

              have F: "perm (Out B) ((Out B \<otimes> In B) @ (Out B \<ominus> In B))"
                by (metis OB''_def Var_def \<open>perm (Out B) (Var B B @ OB'')\<close>)
              have G: "perm (Out B \<ominus> In B) (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                by (metis diff_sym perm_diff_left_inter)
              have H: "((Out B \<ominus> In B) \<otimes> In A) = (Out B \<otimes> In A)"
                apply (simp add: diff_filter inter_filter)
                apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
                apply (metis diff_distinct diff_filter filter_id_conv)
                by simp
              have I: "perm (Out B \<ominus> In B) ((Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out B \<ominus> In B) (((Out B \<ominus> In B) \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                 apply (subgoal_tac "((Out B \<ominus> In B) \<otimes> In A) = (Out B \<otimes> In A)")
                  apply simp
                apply (simp only: H)
                by (simp only: G)
              
              have J: "perm (Out B)  ((Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
                apply (subgoal_tac "perm (Out B) ((Out B \<otimes> In B) @ (Out B \<ominus> In B))")
                 apply (subgoal_tac "perm (Out B \<ominus> In B) ((Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                  apply (metis perm_mset union_code)
                apply (simp only: I)
                by (simp only: F)
             
             show "perm (Out A @ Out B) ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B) @ (Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))"
              apply (subgoal_tac "perm (Out A)  ((Out A \<otimes> In A) @ (Out A \<otimes> In B) @ (Out A \<ominus> In A \<ominus> In B))")
                apply (subgoal_tac "perm (Out B)  ((Out B \<otimes> In B) @ (Out B \<otimes> In A) @ (Out B \<ominus> In A \<ominus> In B))")
                 apply (metis append.assoc perm_mset union_code)
              apply (simp only: J)
              by (simp only: E)
          qed

         have [simp]: "set IB'' \<subseteq> set (Var A B) \<union> set IB'"
            apply (simp add: IB''_def IB'_def set_diff Var_def set_inter)
            by blast

         have [simp]: "distinct OB''"
            by (simp add: OB''_def)

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
            by (simp_all)

         have [simp]: "TO (Trs (FB A)) = TVs OA''"
            apply (simp add: FB_def Let_def OA''_simp)
            apply (cut_tac t="TVs (Var A A)" and ts="TVs(In A \<ominus> Var A A)" and ts'="TVs(Out A \<ominus> Var A A)" and
                S="([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])" in  TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var A A)) = length (Var A A)")
            by simp_all

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
            by (simp add: )

         have [simp]: "TO (Trs (FB B)) = TVs OB''"
            apply (simp add: FB_def Let_def OB''_simp)
            apply (cut_tac t="TVs (Var B B)" and ts="TVs(In B \<ominus> Var B B)" and ts'="TVs(Out B \<ominus> Var B B)" and
                S="([Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out B \<ominus> Var B B)])" in  TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            apply (simp)
            by (simp add: )

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
            by (simp_all)

          have [simp]: "TO ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) = TVs (Var A B) @ TVs OA'"
            apply (cut_tac t="(TVs (Var A A))" and S="[Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA']" and ts="TVs(Var B A @ IA')" and ts'="TVs(Var A B @ OA')" in TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var A A) = length (TVs (Var A A))")
              using TVs_append apply presburger
            by (simp add: TO_fb)

          have [simp]: "TI ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) = TVs (Var A B) @ TVs IB'"
            apply (cut_tac t="(TVs (Var B B))" and S="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" in TI_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var B B) = length (TVs (Var B B))")
              using TVs_append apply presburger
            by (simp add: TO_fb)
          
          have [simp]: "TO ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) = TVs (Var B A) @ TVs OB'"
            apply (cut_tac t="(TVs (Var B B))" and S="[Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB']" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" in TO_fb_fbtype_n)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (Var B B) = length (TVs (Var B B))")
              using TVs_append apply presburger
            by (simp add: TO_fb)

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
            by (simp add: IA''_def)

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
            apply (simp)
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
            apply (subgoal_tac "io_diagram A")
            apply (subgoal_tac "io_diagram B")
            apply (subgoal_tac "set (In A) \<inter> set (In B) = {}")
            apply (simp add: perm_var_Par perm_sym)
            by simp_all

         
          have FB_Par_A_B: "FB (A ||| B) = 
            \<lparr>In = I, Out = O', Trs = (fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] 
            oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'])  \<rparr>"
            (is "_ = \<lparr>In=I,Out=O',Trs = ?T\<rparr>")

            by (simp add: FB_def Let_def I_def O'_def) 
              
          thm fb_perm_eq
          thm I_def
            
            have "[(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']
            = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo ([Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'] oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'])"
              by (simp add: comp_assoc [THEN sym]) 
            also have "... = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']"
                  apply (subgoal_tac "[Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'] oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] = [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']")
                   apply simp
                  apply (subst switch_comp, simp_all)
                   apply (metis BaseOperationFeedbacklessVars.Parallel_def BaseOperationFeedbacklessVars.Var_def BaseOperationFeedbacklessVars_axioms O'_def mset_inter_diff perm_mset simps(2) union_code)
                  by (simp add: O'_def Var_def  set_addvars set_diff set_inter, auto)
                    
                also have "... = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O']"
                  apply (subgoal_tac " [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              [Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] = [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)]")
                   apply simp
                  apply (subst switch_comp, simp_all)
                  using aa apply auto[1]
                  by (simp add: I_def Var_def  set_addvars set_diff set_inter)
                    
                    
                    
                    
                finally have ZZZ: "[(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] 
                oo ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] =
              [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] "
             by simp
                    
                    
                 
                
            
          from fb_perm_eq have fb_perm_eq_a: "\<And> x . perm x (VarFB (A ||| B)) \<Longrightarrow> (fb ^^ length (VarFB (A ||| B))) ([VarFB (A ||| B) @ InFB (A ||| B) \<leadsto> In A \<oplus> In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> VarFB (A ||| B) @ OutFB (A ||| B)]) =
        (fb ^^ length (VarFB (A ||| B))) ([x @ InFB (A ||| B) \<leadsto> In A \<oplus> In B] oo Trs (A ||| B) oo [Out A @ Out B \<leadsto> x @ OutFB (A ||| B)]) "
            by (simp add: fb_perm_eq_def )
             
          have "?T = (fb ^^ length (Var (A ||| B) (A ||| B))) (
              [(Var A A @ Var B B @ Var A B @ Var B A) @ I \<leadsto> Var (A ||| B) (A ||| B) @ I] oo 
              ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O']) oo
              [Var (A ||| B) (A ||| B) @ O' \<leadsto> (Var A A @ Var B B @ Var A B @ Var B A) @ O'] )" (is "_ = ?Fb (?Sa oo (?Sb oo ?Tr oo ?Sc) oo ?Sd)")
            apply (subst ZZZ)
            apply (cut_tac fb_perm_eq_a[of "Var A A @ Var B B @ Var A B @ Var B A"])
             apply (simp add: O'_def I_def OutFB_def VarFB_def InFB_def)
              by (metis VarFB_def aa append_assoc perm_append2_eq)

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
            apply (subst switch_comp, simp_all add: Var_def set_inter setI Parallel_def O'_def)
              apply (metis (no_types, lifting) mset_inter_diff perm_mset union_code)
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
              apply (simp add: addvars_def diff_distinct)
            apply (simp add: Parallel_indep)
            apply (subst comp_assoc)
            by (simp_all)
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
            by (simp_all add: Parallel_indep)
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
              apply presburger
            by simp
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
            by (simp_all add: fbtype_def)
          also have "... = (fb ^^ length (Var B A)) ((fb ^^ length (Var A B)) 
                ( [Var A B @ Var B A @ I \<leadsto> Var A B @ IB' @ Var B A @ IA'] oo
                    ((fb ^^ length (Var B B)) ([Var B B @ Var A B @ IB'  \<leadsto> In B]  oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])) \<parallel> ((fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])) oo
                  [Var B A @ OB' @ Var A B @ OA' \<leadsto> Var A B @ Var B A @ O']))"  (is "_ = ?Fd (?Sk oo ?Sl \<parallel> ?Sm oo ?Sn) " )             
            apply (cut_tac tsa="TVs(Var B B)" and ts="TVs(Var A B @ IB')" and ts'="TVs(Var B A @ OB')" and 
                S="([Var B B @ Var A B @ IB' \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ Var B A @ OB'])" and
                T= "(fb ^^ length (Var A A)) ([Var A A @ Var B A @ IA' \<leadsto> In A] oo Trs A oo [Out A \<leadsto> Var A A @ Var A B @ OA'])" in fb_gen_parallel)
            apply (simp add: fbtype_def)
            apply (subgoal_tac "length (TVs (Var B B)) = length (Var B B)")
            by (simp_all)
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
            by (simp_all)
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
            by (simp )
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
            by (simp_all add: distinct_id)
          also have "... = ?Fe (?So oo 
                ID (TVs OA') \<parallel> ([Var A B @ IB' \<leadsto> IB''] oo Trs (FB B) oo  [OB'' \<leadsto> Var B A @ OB'])
                oo ?Sp)" (is "_ = ?Fe (?Sq oo ?Sr oo ?St oo ?Sp)")
            apply (subst(3) FB_def)
            apply (simp add: Let_def)
            apply (subgoal_tac "IB'' = (In B \<ominus> Var B B)")
            apply (subgoal_tac "OB'' = (Out B \<ominus> Var B B)")
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
          also have Az: "... = Trs (FB (FB (A) ;; FB (B)))"
            apply (subst(3) FB_def)
            apply (simp add: Let_def In_FB_simp Out_FB_simp)
            by (simp add: Var_FB_simp)

          finally have A: "(fb ^^ length (Var (A ||| B) (A ||| B))) ([Var (A ||| B) (A ||| B) @ I \<leadsto> In (A ||| B)] oo Trs (A ||| B) oo [Out (A ||| B) \<leadsto> Var (A ||| B) (A ||| B) @ O'])
              =  Trs (FB (FB (A) ;; FB (B)))"
            by simp

       show "FB (A ||| B) = FB (FB (A) ;; FB (B))"
          proof -
            have "FB (A ||| B) = \<lparr>In = In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B), Out = Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B), Trs 
          = (fb ^^ length (Var (FB A ;; FB B) (FB A ;; FB B))) 
                ([Var (FB A ;; FB B) (FB A ;; FB B) @ (In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B)) \<leadsto> In (FB A ;; FB B)] oo Trs (FB A ;; FB B) 
              oo [Out (FB A ;; FB B) \<leadsto> Var (FB A ;; FB B) (FB A ;; FB B) @ (Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B))])\<rparr>"
              
              
              using A I_def In_FB_simp In_simp Out_FB_simp Var_FB_simp Az FB_Par_A_B 
               \<open>In (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B) = IA' @ IB'\<close> 
               \<open>Out (FB A ;; FB B) \<ominus> Var (FB A ;; FB B) (FB A ;; FB B) = O'\<close> by auto
              
            then show ?thesis
              by (metis FB_def)
          qed
        qed
          
declare io_diagram_distinct [simp del]  

    
lemma in_out_equiv_FB_less: "io_diagram B \<Longrightarrow> in_out_equiv A B \<Longrightarrow> fb_perm_eq A \<Longrightarrow>  in_out_equiv (FB A) (FB B)"
      proof -
        assume A: "io_diagram B"
        assume B: "in_out_equiv A B"
          
        have [simp]: "perm (Var A A) (Var B B)"
          apply (simp add: Var_def)
          using B in_out_equiv_def perm_ops by blast
            
        from this have [simp]: "perm (Var B B) (Var A A)"
          by (rule perm_sym)

        have [simp]: "length (Var A A) = length (Var B B)"
          using [[simp_trace]]
          using A B apply (unfold io_diagram_def in_out_equiv_def)
          apply (simp add:  Var_def)
          apply (subgoal_tac "perm (Out A \<otimes> In A) (Out B \<otimes> In B)")
          using perm_length apply blast
          by simp
        have [simp]: "TI (Trs B) = TVs (In B)" and [simp]: "TO (Trs B) = TVs (Out B)" and [simp]: "distinct (In A)" and [simp]: "distinct (Out A)" 
          and [simp]: "distinct (Out B)" and [simp]: "perm (Out B) (Out A)"
          using A B apply (simp_all add: io_diagram_def in_out_equiv_def Var_def perm_sym)
          using dist_perm perm_sym apply blast
          using dist_perm perm_sym by blast
            
        have "perm (In A) (In B)"
          using B in_out_equiv_def by blast
         
        from this have [simp]: "set (In B) \<subseteq> set (In A)"
          by simp

        from B have X: "Trs A = [In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]"
          by (simp add: in_out_equiv_def)
            
        from this have Y: "\<And> x y . perm x (In A) \<Longrightarrow> perm y (Out A) \<Longrightarrow> [x \<leadsto> In A] oo Trs A oo [Out A \<leadsto> y]
            = [x \<leadsto> In B] oo Trs B oo [Out B \<leadsto> y]"
        proof -
          fix x y
          assume "perm x (In A)"
          assume "perm y (Out A)"
          have "[x \<leadsto> In A] oo Trs A oo [Out A \<leadsto> y] = [x \<leadsto> In A] oo ([In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]) oo [Out A \<leadsto> y]"
            by (simp add: X)
          also have "... = ([x \<leadsto> In A] oo [In A \<leadsto> In B]) oo Trs B oo ([Out B \<leadsto> Out A] oo [Out A \<leadsto> y])"
            by (simp add: comp_assoc)
          also have "... = [x \<leadsto> In B] oo Trs B oo [Out B \<leadsto> y]"
            by (metis \<open>distinct (In A)\<close> \<open>distinct (Out B)\<close> \<open>perm (Out B) (Out A)\<close> \<open>perm x (In A)\<close> \<open>perm y (Out A)\<close> \<open>set (In B) \<subseteq> set (In A)\<close> dist_perm order_refl perm_set_eq perm_sym switch_comp)
          finally show "[x \<leadsto> In A] oo Trs A oo [Out A \<leadsto> y] = [x \<leadsto> In B] oo Trs B oo [Out B \<leadsto> y]"
            by simp
        qed
          
        have [simp]: "perm (Var B B @ (In A \<ominus> Var A A)) (In A)"
          by (metis (no_types, lifting) Var_def \<open>distinct (In A)\<close> \<open>distinct (Out B)\<close> \<open>perm (In A) (In B)\<close> \<open>perm (Out B) (Out A)\<close> diff_inter_right list_inter_set perm_diff_eq perm_set_eq perm_switch_aux_f)
             
        have [simp]: "perm (Var B B @ (Out A \<ominus> Var A A)) (Out A)"
          by (metis Var_def \<open>distinct (In A)\<close> \<open>distinct (Out A)\<close> \<open>perm (Var B B) (Var A A)\<close> diff_inter_left perm_mset perm_switch_aux_c union_code)

        assume "fb_perm_eq A"
        from this have H: "(fb ^^ length (Var B B)) ([Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)]) =
              (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
          apply (simp add:fb_perm_eq_def InFB_def VarFB_def OutFB_def)
          apply (drule_tac x = "Var B B" in spec)
          by (simp add:  Y)
            
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
          by (metis A Var_def diff_inter_left perm_switch_aux_c perm_sym io_diagram_def)
        have [simp]: " set (Out A \<ominus> Var A A) \<subseteq> set (Var B B) \<union> set (Out B \<ominus> Var B B)"
          using \<open>set (Out A \<ominus> Var A A) \<subseteq> set (Out B \<ominus> Var B B)\<close> by blast
        have [simp]: "perm (Var A A @ (In A \<ominus> Var A A)) (Var B B @ (In A \<ominus> Var A A))"
          using \<open>perm (Var A A) (Var B B)\<close> perm_union_left by blast
        have [simp]: "set (In B) \<subseteq> set (Var B B) \<union> set (In A \<ominus> Var A A)"
          using \<open>set (In B \<ominus> Var B B) \<subseteq> set (In A \<ominus> Var A A)\<close> \<open>set (In B) \<subseteq> set (Var B B) \<union> set (In B \<ominus> Var B B)\<close> by blast
        have [simp]: "perm (Out B) (Var B B @ (Out A \<ominus> Var A A))"
          by (meson \<open>perm (Out B) (Out A)\<close> \<open>perm (Out B) (Var B B @ (Out B \<ominus> Var B B))\<close> \<open>perm (Var A A) (Var B B)\<close> perm_diff perm_sym perm_trans perm_union_right)
        have [simp]: "set (Var A A) \<subseteq> set (Var B B) \<union> set (Out A \<ominus> Var A A)"
          using ListProp.perm_set_eq \<open>Var A A <~~> Var B B\<close> by blast

        have C: "ID (TVs (Var B B)) \<parallel> [In A \<ominus> Var A A \<leadsto> In B \<ominus> Var B B] oo [Var B B @ (In B \<ominus> Var B B) \<leadsto> In B] =  [Var B B @ (In A \<ominus> Var A A) \<leadsto> In B]"
          
          apply (subst distinct_id [THEN sym])
            apply (simp_all add: par_switch switch_comp)
          apply (subst switch_comp, simp_all)
            using \<open>In A <~~> In B\<close> by auto
              
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
            apply (simp_all add: fbtype_def)
            apply (simp add: )
          by (simp add: comp_assoc)
        also have "... = (fb ^^ length (Var B B)) ([Var B B @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var B B @ (Out A \<ominus> Var A A)])"
        by (simp add: C D)
      
      also have "... = (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
        by (simp add: H)
      also from B have "... = (fb ^^ length (Var B B)) ([Var A A @ (In A \<ominus> Var A A) \<leadsto> In A] oo ([In A \<leadsto> In B] oo Trs B oo [Out B \<leadsto> Out A]) oo [Out A \<leadsto> Var A A @ (Out A \<ominus> Var A A)])"
          apply (simp add: comp_assoc [THEN sym] switch_comp in_out_equiv_def)
          by (simp add: comp_assoc switch_comp)

      finally show ?thesis
        using A B apply (simp add: FB_def in_out_equiv_def Let_def)
        by (simp add: comp_assoc [THEN sym] switch_comp)
    qed

lemma [simp]: "io_diagram A \<Longrightarrow> distinct (OutFB A)"
  by (simp add: OutFB_def io_diagram_distinct(2))



end

end