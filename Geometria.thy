(*<*)
theory Geometria
imports Main  "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*)

(* ---------------------------------------------------------------------  
                  FORMALISING AND REASONING                  
                ABOUT GEOMETRIES USING LOCALES                
   ------------------------------------------------------------------ *)

section \<open>Introducción a la geometría \<close>

text \<open>La geometría posee una larga de historía de estar presentada y
 representada por sistemas axiomáticos, es decir, cualquier conjunto de
 axiomas a partir del cual se pueden usar algunos o todos los axiomas en
 conjunto para derivar lógicamente teoremas. Un axioma es una
 declaración que se considera verdadera, que sirve como punto 
de partida para razonamientos y argumentos adicionales.


 Por ello, vamos a representar la geometria simple, que la entenderemos
 definiendo el  plano como un conjunto de puntos y las líneas como 
conjuntos de puntos, la geometría no proyectiva añadiéndole un axioma a 
la simple y por  último, la geometria proyectiva añadiendole 3 axiomas 
a la simple. 

Todo esto se definirá en Isabelle/HOL como un entorno local. Un entorno
 local o declaración local consiste en secuencia de elementos que
 declararán parámetros(\textbf{fixed}) y suposiciones
 (\textbf{assumption}).


\<close>
(* --------------------------------------------------------------------
   Problem 14: State formally the following axioms.  
  ------------------------------------------------------------------- *)

section \<open>Geometría simple \<close>

subsection \<open>Entorno local \<close>

text \<open> 

La geometría simple, como ya se ha nombrado anteriormente, posee tres
 elementos fundamentales. Los puntos, el plano, que es el conjunto de
 todos ellos, y las rectas, que son conjuntos de puntos. Esta geometría
 posee 5 axiomas:


\begin{enumerate}

\item{El plano es no vacío.}

\item{Toda línea es un subconjunto no vacío del plano.}

\item{Para cualquier par de puntos en el plano, existe una línea que
 contiene a ambos.}

\item{Dos líneas diferentes intersecan en no mas de un punto.}

\item{Para toda línea, existe un punto del plano que no pertenece a
 ella.}
\end{enumerate}

Se ha declarado un entorno local, denotado \textbf{Simple$-$Geometry}, con
un par de constantes(\textbf{lines} y \textbf{plane}) junto con los 5
 axiomas ya definidos anteriormente.
\<close>

locale Simple_Geometry =
  fixes plane :: "'a set"
  fixes lines :: "('a set) set"
  assumes A1: "plane \<noteq> {}"
      and A2: "\<forall>l \<in> lines. l \<subseteq> plane \<and> l \<noteq> {}"
      and A3: "\<forall>p \<in> plane. \<forall>q \<in> plane. \<exists>l \<in> lines. {p,q} \<subseteq> l"
      and A4: "\<forall>l \<in> lines. \<forall>r \<in> lines.
               l \<noteq> r  \<longrightarrow>  l \<inter> r = {} \<or> (\<exists>q \<in> plane. l \<inter> r = {q}) "
               (* Two different lines intersect in no more than one 
                  point. *)
      and A5: "\<forall>l \<in> lines. \<exists>q \<in> plane. q \<notin> l"
              (* For every line L there is a point in the plane outside 
                 of L. *)


text \<open>
A pesar de la definición del entorno local goemetría simple de 5
 axiomas, no en todas las demostraciones, se van a usar todos ellos. Sin
embardo, al haber definido tanto las lineas como el plano como conjuntos
 tenemos todas las funciones definidas en Isabelle/HOL de la teoría de
 conjuntos
  \href{https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/HOL/HOL/Set.html}{Set.thy}.
\<close>


subsection \<open>
Proposiciones de geometría simple
\<close>

(* ---------------------------------------------------------------------
   Problem 15 : Formalise the statement: the set of lines is non-empty 
   ------------------------------------------------------------------ *)

lemma (in Simple_Geometry) one_line_exists:
  "\<exists>l. l \<in> lines " 
proof - 
  have "\<exists>q. q \<in> plane " using A1 by auto
  then obtain "q1" where "q1 \<in> plane" by (rule exE)
  then obtain "\<exists>l \<in> lines. {q1, q1} \<subseteq> l" using A3 by auto
  then show ?thesis by auto
qed

(* ---------------------------------------------------------------------
   Problem 16
   ------------------------------------------------------------------ *)

lemma (in Simple_Geometry) two_points_exist:
  "\<exists>p1 p2. p1 \<noteq> p2 \<and> {p1, p2} \<subseteq> plane"
proof -
  obtain "l1" where "l1 \<in> lines" 
    using one_line_exists by (rule exE)
  then obtain "l1 \<subseteq> plane \<and> l1 \<noteq> {}" 
    using A2 by auto
  then have "\<exists>q. q \<in> l1 \<and> q \<in> plane" 
    by auto
  then obtain "p1" where "p1 \<in> l1 \<and> p1 \<in> plane" 
    by (rule exE)
  moreover obtain "p2" where "p2 \<in> plane \<and> p2 \<notin> l1" 
    using \<open>l1 \<in> lines\<close> A5 by auto
  ultimately show ?thesis  
    by force 
qed

(* --------------------------------------------------------------------- 
   Problem 17 
   ------------------------------------------------------------------ *)

lemma (in Simple_Geometry) three_points_exist:
  "\<exists>p1 p2 p3. distinct [p1, p2, p3] \<and> {p1, p2, p3} \<subseteq> plane" 
proof - 
  obtain "p1" "p2"  where  "p1 \<noteq> p2 \<and> {p1, p2} \<subseteq> plane"
    using two_points_exist by auto  
  moreover then obtain "l1" where "l1 \<in> lines \<and> {p1, p2} \<subseteq> l1" 
    using A3 by auto
  moreover then obtain "p3" where "p3 \<in> plane \<and> p3 \<notin> l1" 
    using A5 by auto
  ultimately have "distinct [p1, p2, p3] \<and> {p1, p2, p3} \<subseteq> plane" 
    by auto
  then show ?thesis 
    by (intro exI)
qed

(* ---------------------------------------------------------------------  
   Problem 18 
   ------------------------------------------------------------------ *)

lemma (in Simple_Geometry) card_of_plane_greater:
  assumes "finite plane" 
  shows "card plane \<ge> 3"
proof -
  obtain "p1" "p2" "p3" where 
    "distinct [p1, p2, p3] \<and> {p1, p2, p3} \<subseteq> plane"
    using three_points_exist by auto
  moreover then have "{p1, p2, p3} \<subseteq> plane"  
    by (rule conjE)
  then have "card {p1, p2, p3} \<le> card plane" 
    using assms by (simp add: card_mono)
  ultimately show ?thesis  by auto
qed

(* --------------------------------------------------------------------- 
   Problem 19
   ------------------------------------------------------------------ *)

subsection \<open>
Interpretación mínimo modelo geometría simple 
\<close>
definition "plane_3 \<equiv> {1::nat,2,3} "

definition "lines_3 \<equiv> {{1,2},{2,3},{1,3}}"

interpretation Simple_Geometry_smallest_model:
  Simple_Geometry plane_3 lines_3
  apply standard 
      apply (simp add: plane_3_def lines_3_def)+
  done

(* ---------------------------------------------------------------------
   Problem 20
   ------------------------------------------------------------------ *)

lemma (in Simple_Geometry) how_to_produce_different_lines:
  assumes
    "l \<in> lines" 
    "{a, b} \<subseteq> l" "a \<noteq> b"
    "p \<notin> l"
    "n \<in> lines" "{a, p} \<subseteq> n" 
    "m \<in> lines" "{b, p} \<subseteq> m"
  shows "m \<noteq> n"
proof (rule notI)
  assume "m = n"
  show False
  proof -
    have "m \<noteq> l" 
      using assms(4, 8) by auto
    moreover have "l \<noteq> m  \<longrightarrow>  l \<inter> m = {} \<or> (\<exists>q \<in> plane. l \<inter> m = {q})"
      using assms(1, 7) A4 by auto
    ultimately have "l \<inter> m = {} \<or> (\<exists>q \<in> plane. l \<inter> m = {q})"   
      by auto
    then show False 
    proof (rule disjE)
      assume "l \<inter> m = {}"
      then show False 
        using assms(2, 6) \<open>m = n\<close> by auto
    next
      assume "\<exists>q \<in> plane. l \<inter> m = {q}" 
      then obtain "q" where "q \<in> plane \<and> l \<inter> m = {q}" 
        by auto
      then have "l \<inter> m = {q}" 
        by (rule conjE)
      then have "{a, b} \<subseteq> {q}" 
        using assms(2, 6, 8) \<open>m = n\<close> by auto
      then show False 
        using assms(3) by auto
    qed
  qed
qed

(* --------------------------------------------------------------------- 
   Problem 21   
   ------------------------------------------------------------------ *)

lemma (in Simple_Geometry) how_to_produce_different_points:
  assumes
    "l \<in> lines" 
    "{a, b} \<subseteq> l" "a \<noteq> b"
    "p \<notin> l"
    "n \<in> lines" "{a, p, c} \<subseteq> n"  
    "m \<in> lines" "{b, p, d} \<subseteq> m"
    "p \<noteq> c"
  shows "c \<noteq> d" 
proof 
  assume "c = d" 
  show False
  proof -
    have "m \<noteq> n" 
      using assms how_to_produce_different_lines by simp
    moreover have "n \<noteq> m  \<longrightarrow>  m \<inter> n = {} \<or> (\<exists>q \<in> plane. m \<inter> n = {q})"
      using assms(5,7) A4 by auto
    ultimately have "m \<inter> n = {} \<or> (\<exists>q \<in> plane. m \<inter> n = {q})" 
      by auto
    then show False
    proof (rule disjE)
      assume "m \<inter> n = {}"
      then show False 
        using assms(6, 8) by auto
    next
      assume "\<exists>q \<in> plane. m \<inter> n = {q}"
      then obtain "q" where "q \<in> plane \<and> m \<inter> n = {q}" 
        by auto
      then have "{p,d} \<subseteq> {q}" 
        using \<open>c = d\<close> assms by auto
      then show False 
        using \<open>c = d\<close> assms(9) by auto
    qed
  qed
qed

section \<open>Geometría no proyectiva \<close>

(* ---------------------------------------------------------------------
   Problem 22: Formalise the following axiom: 
     if a point p lies outside of line l then there must exist at least
     one line m that passes through p, which does not intersect l 
  ------------------------------------------------------------------- *)
subsection \<open>Entorno local \<close>
locale Non_Projective_Geometry =
  Simple_Geometry +
  assumes parallels_Ex:
    "\<forall>p \<in> plane. \<forall>l \<in> lines. p \<notin> l \<longrightarrow> (\<exists>m \<in> lines. p \<in> m \<and> m \<inter> l = {} )"

(* ---------------------------- ----------------------------------------
   Problem 23: Give a model of Non-Projective Geometry with 
   cardinality 4. 
   Show that it is indeed a model using the command "interpretation" 
   ------------------------------------------------------------------ *)

subsection \<open>Interpretacion modelo geometría no proyectiva \<close>
definition "plane_4 \<equiv> {1::nat, 2, 3, 4}"

definition "lines_4 \<equiv> {{1,2},{2,3},{1,3},{1,4},{2,4},{3,4}}"

interpretation Non_projective_geometry_card_4:
  Non_Projective_Geometry plane_4 lines_4
  apply standard
       apply (simp add: plane_4_def lines_4_def)+
  done

(* ---------------------------------------------------------------------
   Problem 24: Formalise and prove: 
     "it is not true that every pair of lines intersect"  
  ------------------------------------------------------------------- *)

subsection \<open>Proposiciones de geometría no proyectiva \<close>
lemma (in Non_Projective_Geometry) non_projective:
  "\<not>(\<forall>r \<in> lines. \<forall>s \<in> lines. r \<inter> s \<noteq> {})"
proof 
  assume 4: "\<forall>r\<in>lines. \<forall>s\<in>lines. r \<inter> s \<noteq> {}"
  show False
  proof -
    obtain "l1" where 1: "l1 \<in> lines" 
      using one_line_exists by auto
    then obtain "q1" where 2: "q1 \<in> plane \<and> q1 \<notin> l1" 
      using A5 by auto
    then have "q1 \<notin> l1 \<longrightarrow> (\<exists>m \<in> lines. q1 \<in> m \<and> m \<inter> l1 = {} )" 
      using 1 parallels_Ex by simp
    then obtain "m1" where 3: "m1 \<in> lines \<and> q1 \<in> m1 \<and> m1 \<inter> l1 = {}"
      using 2 by auto
    then obtain "m1 \<inter> l1 \<noteq> {}" using 1 4 by auto
    then show ?thesis using 3 by auto
  qed
qed

(* The following are some auxiliary lemmas that may be useful.
   You don't need to use them if you don't want. *)

lemma construct_set_of_card1:
  "card x = 1 \<Longrightarrow> \<exists> p1. x = {p1}"
  by (metis One_nat_def card_eq_SucD)

lemma construct_set_of_card2:
  "card x = 2 \<Longrightarrow> \<exists> p1 p2 . distinct [p1,p2] \<and> x = {p1,p2}" 
  by (metis card_eq_SucD distinct.simps(2) 
      distinct_singleton list.set(1) list.set(2) numeral_2_eq_2)

lemma construct_set_of_card3:
  "card x = 3 \<Longrightarrow> \<exists> p1 p2 p3. distinct [p1,p2,p3] \<and> x = {p1,p2,p3}" 
  by (metis card_eq_SucD distinct.simps(2) 
      distinct_singleton list.set(1) list.set(2) numeral_3_eq_3)

lemma construct_set_of_card4:
  "card x = 4 \<Longrightarrow> \<exists> p1 p2 p3 p4. distinct [p1,p2,p3,p4] \<and> x = {p1,p2,p3,p4}" 
  by (metis (no_types, lifting) card_eq_SucD construct_set_of_card3 
      Suc_numeral add_num_simps(1) add_num_simps(7) 
      distinct.simps(2) empty_set list.set(2))


section \<open>Geometría proyectiva \<close>

subsection \<open>
Entorno local 
\<close>
locale Projective_Geometry = 
  Simple_Geometry + 
  assumes A6: "\<forall>l \<in> lines. \<forall>m \<in> lines. \<exists>p \<in> plane. p \<in> l \<and> p \<in> m"
      and A7: "\<forall>l \<in> lines. \<exists>x. card x = 3 \<and> x \<subseteq> l" 

(* ---------------------------------------------------------------------
   Problem 25: Prove this alternative to axiom A7  
   ------------------------------------------------------------------ *)
subsection \<open>Proposiciones de geometría proyectiva \<close>

lemma (in Projective_Geometry) A7a:
  "\<forall>l \<in> lines. \<exists>p1 p2 p3. {p1, p2, p3} \<subseteq> plane \<and> 
                          distinct [p1, p2, p3] \<and> 
                          {p1, p2, p3} \<subseteq> l" 
proof
  fix l
  assume 1: "l \<in> lines"
  show "\<exists>p1 p2 p3. {p1, p2, p3} \<subseteq> plane \<and> 
                   distinct [p1, p2, p3] \<and> 
                   {p1, p2, p3} \<subseteq> l"
  proof -
    obtain x where 2: "card x = 3 \<and> x \<subseteq> l"  
      using 1 A7 by auto
    then have 3: "card x = 3" 
      by (rule conjE)
    have "\<exists> p1 p2 p3. distinct [p1, p2, p3] \<and> x = {p1, p2, p3}" 
      using 3 by (rule construct_set_of_card3)
    then obtain "p1" "p2" "p3" 
      where 4 :"distinct [p1,p2,p3] \<and> x = {p1, p2, p3}" 
      by auto
    obtain "l \<subseteq> plane \<and> l \<noteq> {}" 
      using 1 A2  by auto
    then have 
      "{p1, p2, p3} \<subseteq> plane \<and> distinct [p1, p2, p3] \<and> {p1, p2, p3} \<subseteq> l"
      using 4 2 by auto
    then show ?thesis 
      by auto
  qed
qed

(* ---------------------------------------------------------------------
   Problem 26: Prove yet another alternative to axiom A7  
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) A7b: 
  assumes "l \<in> lines"
    "{p, q} \<subseteq> l " 
  shows   "\<exists>r \<in> plane. r \<notin> {p, q} \<and> r \<in> l" 
proof -
  obtain "x" where 1: "card x = 3 \<and> x \<subseteq> l" 
    using assms A7 by auto
  then have "card x = 3" 
    by (rule conjE)
  then have "\<exists> p1 p2 p3. distinct [p1,p2,p3] \<and> x = {p1,p2,p3}" 
    by (rule construct_set_of_card3)
  then obtain "p1" "p2" "p3" 
    where 2: "distinct [p1,p2,p3] \<and> x = {p1,p2,p3}" 
    by auto
  have "l \<subseteq> plane \<and> l \<noteq> {}" 
    using A2 assms by auto
  then have 3: "x \<subseteq> plane" 
    using 1 by auto
  then have "p1 \<notin> {p,q} \<or> p2 \<notin> {p,q} \<or> p3 \<notin> {p,q}" 
    using 2 by auto
  then show ?thesis using 1 2 3 by auto
qed
      
(* ---------------------------------------------------------------------
   Problem 27
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) two_lines_per_point:
  "\<forall>p \<in> plane. \<exists>l \<in> lines. \<exists>m \<in> lines. l \<noteq> m \<and> p \<in> l \<inter> m" 
proof 
  fix p 
  assume 1: "p \<in> plane"
  show "\<exists>l \<in> lines. \<exists>m \<in> lines. l \<noteq> m \<and> p \<in> l \<inter> m" 
  proof -
    obtain l where 2: "l \<in> lines \<and> {p,p} \<subseteq> l" 
      using A3 1 by auto
    then obtain r where 3: "r \<notin> l \<and> r \<in> plane" 
      using A5 by auto
    then obtain m where 4: "m \<in> lines \<and> {p,r} \<subseteq> m " 
      using A3 1  by auto
    then have "l \<noteq> m \<and> p \<in> l \<inter> m" 
      using  2 3 by auto
    then show ?thesis 
      using 2 4 by auto
  qed
qed

(* ---------------------------------------------------------------------
   Problem 28
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) external_line:
  "\<forall>p \<in> plane. \<exists>l \<in> lines. p \<notin> l" 
proof 
  fix p 
  assume 1: "p \<in> plane" 
  show "\<exists>l \<in> lines. p \<notin> l"
  proof - 
    obtain l1 where 2: "l1 \<in> lines \<and> {p,p} \<subseteq> l1" 
      using 1 A3 by auto
    then obtain r where 3: "r \<in> plane \<and> r \<notin> l1" 
      using A5 by auto
    then have "p \<noteq> r" 
      using 2 by auto
    obtain l2 where 4: "l2 \<in> lines \<and> {p,r} \<subseteq> l2" 
      using 1 3 A3 by auto
    then obtain s where 5: "s \<in> plane \<and> s \<notin> l2" 
      using A5 3 by auto
    then have "r \<noteq> s" 
      using 4 by auto
    obtain l where 6: "l \<in> lines \<and> {r,s} \<subseteq> l" 
      using 3 5 A3 by auto
    have "p \<notin> l" 
    proof 
      assume 7: "p \<in> l" 
      have "l \<noteq> l2" 
        using 5 4 6 by auto
      then have "l \<inter> l2 = {} \<or> (\<exists>q \<in> plane. l \<inter> l2 = {q})"
        using A4 4 6 by auto
      then show False
      proof 
        assume "l \<inter> l2 = {}" 
        thus False 
          using 7 4 by auto
      next
        assume "\<exists>q\<in>plane. l \<inter> l2 = {q} "
        then obtain t where 8: "l \<inter> l2 = {t} \<and> t \<in> plane" 
          by auto
        have "{p,r} \<subseteq> l \<inter> l2" 
          using 7 6 4 by auto
        then have "{p,r} \<subseteq> {t}" 
          using 8 by auto
        then show False 
          using 2 3 by auto
      qed
    qed
    then show ?thesis 
      using 6 by auto
  qed
qed

(* --------------------------------------------------------------------
   Problem 29   
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) three_lines_per_point:
  "\<forall>p \<in> plane. \<exists>l m n. 
    distinct [l,m,n] \<and> {l,m,n} \<subseteq> lines \<and> p \<in> l \<inter> m \<inter> n" 
proof 
  fix p 
  assume 1: "p \<in> plane"
  show "\<exists>l m n. distinct [l,m,n] \<and> {l,m,n} \<subseteq> lines \<and> p \<in> l \<inter> m \<inter> n"
  proof - 
    obtain h where 6: "h \<in> lines \<and> p \<notin> h" 
      using 1 external_line by auto
    then obtain a b c 
      where 2: "{a,b,c} \<subseteq> plane \<and> distinct [a,b,c] \<and> {a,b,c} \<subseteq> h"
      using A7a by auto  
    then obtain l where 3: "l \<in> lines \<and> {a,p} \<subseteq> l" 
      using 1 A3 by auto
    obtain m where 4: "m \<in> lines \<and> {b,p} \<subseteq> m" 
      using 1 2 A3 by auto
    obtain n where 5: "n \<in> lines \<and> {c,p} \<subseteq> n" 
      using 1 2 A3 by auto
    have 27: "{m,n,l} \<subseteq> lines" 
      using 3 4 5 by auto
    have 12: "m \<noteq> l" 
    proof 
      assume 7: "m = l" 
      show False
      proof - 
        have 8: "{a,p,b} \<subseteq> l" 
          using 3 4 7 by auto
        have "l \<inter> h = {} \<or> (\<exists>q\<in>plane. l \<inter> h = {q})" 
          using A4 3 6 by auto
        then show False
        proof 
          assume "l \<inter> h = {}" 
          then show False 
            using 8 2 by auto
        next 
          assume "\<exists>q\<in>plane. l \<inter> h = {q}"
          then obtain t where "t \<in> plane \<and> l \<inter> h = {t}" 
            by auto
          then have "{a,b} \<subseteq> {t}" 
            using 8 2 by auto
          then show False 
            using 2 by auto
        qed
      qed
    qed
    have 11: "m \<noteq> n" 
    proof 
      assume 9: "m = n" 
      show False
      proof - 
        have 10: "{b,p,c} \<subseteq> m" 
          using 5 4 9 by auto
        have "m \<inter> h = {} \<or> (\<exists>q\<in>plane. m \<inter> h = {q})" 
          using A4 4 6 by auto
        then show False
        proof 
          assume "m \<inter> h = {}" 
          then show False 
            using 10 2 by auto
        next 
          assume "\<exists>q\<in>plane. m \<inter> h = {q}"
          then obtain t where "t \<in> plane \<and> m \<inter> h = {t}" 
            by auto
          then have "{c,b} \<subseteq> {t}" 
            using 10 2 by auto
          then show False 
            using 2 by auto
        qed
      qed
    qed
    have 13: "l \<noteq> n" 
    proof 
      assume 14: "l = n" 
      show False
      proof - 
        have 15: "{a,p,c} \<subseteq> l" 
          using 3 5 14 by auto
        have "l \<inter> h = {} \<or> (\<exists>q\<in>plane. l \<inter> h = {q})" 
          using A4 6 3 by auto
        then show False
        proof 
          assume "l \<inter> h = {}" 
          then show False 
            using 15 2 by auto
        next 
          assume "\<exists>q\<in>plane. l \<inter> h = {q}"
          then obtain t where "t \<in> plane \<and> l \<inter> h = {t}" 
            by auto
          then have "{a,c} \<subseteq> {t}" 
            using 15 2 by auto 
          then show False 
            using 2 by auto
        qed
      qed
    qed
    have 16: "distinct [n,m,l]" 
      using 11 12 13 by auto  
    have "p \<in> l \<inter> m \<inter> n" 
      using 3 4 5 by auto
    then show ?thesis 
      using 16 27 by auto
  qed
qed

(* ---------------------------------------------------------------------
   Problem 30
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) at_least_seven_points: 
  "\<exists>p1 p2 p3 p4 p5 p6 p7. 
    distinct [p1,p2,p3,p4,p5,p6,p7] \<and> {p1,p2,p3,p4,p5,p6,p7} \<subseteq> plane" 
proof -
  obtain l where 1: "l \<in> lines" 
    using one_line_exists by auto
  then obtain x where 2: "card x = 3 \<and> x \<subseteq> l" 
    using A7 by auto
  then have "card x = 3" 
    by (rule conjE)
  then obtain p1 p2 p3 
    where 3: "distinct [p1,p2,p3] \<and> x = {p1,p2,p3}" 
    using construct_set_of_card3  by metis
  then have 4: "{p1,p2,p3} \<subseteq> l" 
    using 2 by auto
  then have 6: "{p1,p2,p3} \<subseteq> plane" 
    using A2 1 by auto
  obtain q where 5: "q \<in> plane \<and> q \<notin> l"
    using A5 1 by auto
  then have 11: "distinct [p1,p2,p3,q]" 
    using 3 4  by auto
  obtain l1 where 7: "l1 \<in> lines \<and> {p1,q} \<subseteq> l1" 
    using 5 6 A3 by auto
  then have 8: "l1 \<noteq> l" 
    using 5 by auto
  obtain p4 where 9: "p4 \<notin> {p1,q} \<and> p4 \<in> l1" 
    using A7b 7 by metis
  then have 34: "p4 \<in> plane" 
    using A2 7 by auto
  have 17: "p4 \<noteq> p2" 
  proof 
    assume 10: "p4 = p2" 
    have "l \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l \<inter> l1 = {q})" 
      using A4 7 1 8 by auto
    then show False
    proof 
      assume "l \<inter> l1 = {}" 
      then show False 
        using 7 4 by auto
    next 
      assume "\<exists>q\<in>plane. l \<inter> l1 = {q}" 
      then obtain t where "l \<inter> l1 = {t}" 
        by auto
      then have "{p1,p2} \<subseteq> {t}" 
        using 7 4 9 10 by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 18: "p4 \<noteq> p3" 
  proof 
    assume 10: "p4 = p3" 
    have "l \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l \<inter> l1 = {q})" 
      using A4 7 1 8 by auto
    then show False
    proof 
      assume "l \<inter> l1 = {}" 
      then show False 
        using 7 4 by auto
    next 
      assume  "\<exists>q\<in>plane. l \<inter> l1 = {q}" 
      then obtain t where "l \<inter> l1 = {t}" 
        by auto
      then have "{p1,p3} \<subseteq> {t}" 
        using 7 4 9 10 by auto
      then show False 
        using 11 by auto
    qed
  qed
  obtain l2 where 13: "l2 \<in> lines \<and> {p2,q} \<subseteq> l2" 
    using 5 6 A3 by auto
  then obtain p5 where 12: "p5 \<notin> {p2,q} \<and> p5 \<in> l2" 
    using A7b 7 by metis
  then have 35: "p5 \<in> plane" 
    using 13 A2 by auto
  have 27: "l2 \<noteq> l" 
    using 5 13 by auto
  have 19: "p5 \<noteq> p1"  
  proof 
    assume 10: "p5 = p1" 
    have "l \<inter> l2 = {} \<or> (\<exists>q \<in> plane. l \<inter> l2 = {q})" 
      using A4 13 1 27 by auto
    then show False
    proof 
      assume "l \<inter> l2 = {}" 
      then show False 
        using 13 4 by auto
    next 
      assume  "\<exists>q\<in>plane. l \<inter> l2 = {q}" 
      then obtain t where "l \<inter> l2 = {t}" 
        by auto
      then have "{p1,p2} \<subseteq> {t}" 
        using 10 13 12 4 by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 20: "p5 \<noteq> p3" 
  proof 
    assume 10:"p5 = p3" 
    have "l \<inter> l2 = {} \<or> (\<exists>q \<in> plane. l \<inter> l2 = {q})" 
      using A4 13 1 27 by auto
    then show False
    proof 
      assume "l \<inter> l2 = {}" 
      then show False 
        using 13 4 by auto
    next 
      assume "\<exists>q\<in>plane. l \<inter> l2 = {q}" 
      then obtain t where "l \<inter> l2 = {t}" 
        by auto
      then have "{p3,p2} \<subseteq> {t}" 
        using 10 13 12 4 by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 15: "l1 \<noteq> l2" 
  proof 
    assume 14: "l1 = l2" 
    have "l \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l \<inter> l1 = {q})" 
      using A4 7 1 8 by auto
    then show False 
    proof 
      assume "l \<inter> l1 = {}" 
      then show False 
        using 7 4 by auto
    next
      assume "\<exists>q\<in>plane. l \<inter> l1 = {q}" 
      then obtain t where "l \<inter> l1 = {t}" 
        by auto
      then have "{p1,p2} \<subseteq> {t}" 
        using 7 13 14 4  by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 21: "p4 \<noteq> p5" 
  proof 
    assume 16: "p4 = p5"
    have "l2 \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l2 \<inter> l1 = {q})" 
      using A4 7 15 13 by auto
    then show False 
    proof 
      assume "l2 \<inter> l1 = {}"
      then show False 
        using 13 7 by auto
    next
      assume "\<exists>q\<in>plane. l2 \<inter> l1 = {q}"
      then obtain t where "l2 \<inter> l1 = {t}" 
        by auto
      then have "{p4,q} = {t}" 
        using 16 13 7 12 9 by auto
      then show False 
        using 9 by auto
    qed
  qed
  have 29: "distinct [p1,p2,p3,p4,p5,q]" 
    using 11 9 17 18 12 19 20 21 by auto
  obtain l3 where 22: "l3 \<in> lines \<and> {p3,q} \<subseteq> l3" 
    using A3 5 6 by auto
  then obtain p6 where 26: "p6 \<notin> {p3,q} \<and> p6 \<in> l3" 
    using A7b by metis
  then have 36: "p6 \<in> plane" 
    using 22 A2 by auto
  have 23: "l3 \<noteq> l" 
    using 22 5 by auto
  have 30: "p6 \<noteq> p1" 
  proof 
    assume 24: "p6 = p1" 
    have "l3 \<inter> l = {} \<or> (\<exists>q \<in> plane. l3\<inter> l = {q})" 
      using A4 23 22 1 by auto
    then show False
    proof 
      assume "l3 \<inter> l = {}" 
      then show False 
        using 22 4 by auto
    next 
      assume "\<exists>q\<in>plane. l3 \<inter> l = {q}" 
      then obtain t where "l3 \<inter> l = {t}" 
        by auto
      then have "{p1,p3} = {t}" 
        using 24 4 22 26 by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 31: "p6 \<noteq> p2"
  proof 
    assume 24: "p6 = p2" 
    have "l3 \<inter> l = {} \<or> (\<exists>q \<in> plane. l3\<inter> l = {q})" 
      using A4 23 22 1 by auto
    then show False
    proof 
      assume "l3 \<inter> l = {}" 
      then show False 
        using 22 4 by auto
    next 
      assume "\<exists>q\<in>plane. l3 \<inter> l = {q}" 
      then obtain t where "l3 \<inter> l = {t}" 
        by auto
      then have "{p2,p3} = {t}" 
        using 24 4 22 26 by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 25: "l1 \<noteq> l3"
  proof 
    assume 14: "l1 = l3" 
    have "l \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l \<inter> l1 = {q})" 
      using A4 7 1 8 by auto
    then show False 
    proof 
      assume "l \<inter> l1 = {}" 
      then show False 
        using 7 4 by auto
    next
      assume "\<exists>q\<in>plane. l \<inter> l1 = {q}" 
      then obtain t where "l \<inter> l1 = {t}" 
        by auto
      then have "{p1,p3} \<subseteq> {t}" 
        using 7 22 14 4  by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 32: "p6 \<noteq> p4"
  proof 
    assume 16: "p6 = p4"
    have "l3 \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l3 \<inter> l1 = {q})" 
      using A4 7 25 22 by auto 
    then show False
    proof 
      assume "l3 \<inter> l1 = {}"
      then show False 
        using 22 7 by auto
    next
      assume "\<exists>q\<in>plane. l3 \<inter> l1 = {q}"
      then obtain t where "l3 \<inter> l1 = {t}" 
        by auto
      then have "{p4,q} = {t}" 
        using 16 9 26 22 7 by auto
      then show False 
        using 9 by auto
    qed
  qed
  have 28: "l2 \<noteq> l3" 
  proof 
    assume 14: "l2 = l3" 
    have "l \<inter> l2 = {} \<or> (\<exists>q \<in> plane. l \<inter> l2 = {q})" 
      using A4 27 1 13 by auto
    then show False 
    proof 
      assume "l \<inter> l2 = {}" 
      then show False 
        using 13 4 by auto
    next
      assume "\<exists>q\<in>plane. l \<inter> l2 = {q}" 
      then obtain t where "l \<inter> l2 = {t}" 
        by auto
      then have "{p2,p3} \<subseteq> {t}" 
        using 13 22 14 4  by auto
      then show False 
        using 11 by auto
    qed
  qed
  have 33: "p6 \<noteq> p5" 
  proof 
    assume 16: "p6 = p5"
    have "l3 \<inter> l2 = {} \<or> (\<exists>q \<in> plane. l3 \<inter> l2 = {q})" 
      using A4 28 22 13 by auto 
    then show False
    proof 
      assume "l3 \<inter> l2 = {}"
      then show False 
        using 22 13 by auto
    next
      assume "\<exists>q\<in>plane. l3 \<inter> l2 = {q}"
      then obtain t where "l3 \<inter> l2 = {t}" 
        by auto
      then have "{p5,q} = {t}" 
        using 16 12 26 22 13  by auto
      then show False 
        using 29 by auto
    qed
  qed
  have 37: "distinct [p1,p2,p3,p4,p5,p6,q]" 
    using 29 26 30 31 32 33 by auto
  have "{p1,p2,p3,p4,p5,p6,q} \<subseteq> plane" 
    using 6 5 34 35 36 by auto
  then show ?thesis 
    using 37 by metis
qed

subsection \<open>Interpretación modelo geometría proyectiva \<close>

(* ---------------------------------------------------------------------
   Problem 31: Give a model of Projective Geometry with 7 points.
  ------------------------------------------------------------------- *)

definition "plane_7 \<equiv> {1::nat,2,3,4,5,6,7}"

definition "lines_7 \<equiv> {{1,2,3},{1,6,5},{3,4,5},{5,7,2},{3,7,6},
                        {1,4,7},{2,4,6}}"

lemma aux1a: "card {Suc 0, 2, 3} = 3"
  by auto

lemma aux1: "\<exists>x. card x = 3 \<and> x \<subseteq> {Suc 0, 2, 3}"
  using aux1a by blast

lemma aux2a: "card {Suc 0, 6, 5} = 3"
  by auto

lemma aux2: "\<exists>x. card x = 3 \<and> x \<subseteq> {Suc 0, 6, 5}"
  using aux2a by blast

interpretation Projective_Geometry_smallest_model:
  Projective_Geometry plane_7 lines_7
  apply standard 
        apply (simp add: plane_7_def lines_7_def)+
  apply (intro conjI)
  apply (rule aux1)
  apply (rule aux2)
  oops


end
