theory Geometria
imports Main 
begin

(* ---------------------------------------------------------------------  
                  FORMALISING AND REASONING                  
                ABOUT GEOMETRIES USING LOCALES                
   ------------------------------------------------------------------ *)

(* --------------------------------------------------------------------
   Problem 14: State formally the following axioms.  
  ------------------------------------------------------------------- *)


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

definition "plane_3 \<equiv> {1::nat,2,3} "

definition "lines_3 \<equiv> {{1,2},{2,3},{1,3}}"

interpretation Simple_Geometry_smallest_model:
  Simple_Geometry plane_3 lines_3
  apply standard 
      apply (simp add: plane_3_def lines_3_def)+
  done


(*  ----------------------------  *)
(* |   Problem 20 (5 marks):   | *)
(*  ----------------------------  *)
lemma (in Simple_Geometry) 
  how_to_produce_different_lines:
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
    have "m \<noteq> l" using assms(4) assms(8) by auto
    moreover obtain "l \<noteq> m  \<longrightarrow>  l \<inter> m = {} \<or> (\<exists>q \<in> plane. l \<inter> m = {q})"
      using assms(7) A4 assms(1) by auto
    ultimately have "l \<inter> m = {} \<or> (\<exists>q \<in> plane. l \<inter> m = {q})"   by auto
    then show False 
    proof (rule disjE)
      assume "l \<inter> m = {}"
      thus False using assms \<open>m = n \<close> by auto
    next
      assume "\<exists>q \<in>plane. l \<inter> m = {q}" 
      then obtain "q" where "q \<in> plane \<and> l \<inter> m = {q}" by auto
      then have "l \<inter> m = {q}" by (rule conjE)
      then have "{a,b} \<subseteq> {q}" using  assms \<open>m = n \<close> by auto
      then show False using assms(3) by auto
    qed
  qed
qed

(*  ----------------------------  *)
(* |   Problem 21 (4 marks):   | *)
(*  ----------------------------  *)
lemma (in Simple_Geometry) 
  how_to_produce_different_points:
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
    have "m \<noteq> n" using assms how_to_produce_different_lines by simp
    moreover obtain "n \<noteq> m  \<longrightarrow>  m \<inter> n = {} \<or> (\<exists>q \<in> plane. m \<inter> n = {q})"
      using assms(5) assms(7) A4 by auto
    ultimately have "m \<inter> n = {} \<or> (\<exists>q \<in> plane. m \<inter> n = {q})" by auto
      then show False
      proof (rule disjE)
        assume "m \<inter> n = {}"
        then show False using \<open>c = d \<close> assms(6,8) by auto
      next
        assume "\<exists>q\<in>plane. m \<inter> n = {q}"
        then obtain "q" where "q \<in> plane \<and> m \<inter> n = {q}" by auto
        then have "{p,d} \<subseteq> {q}" using \<open>c = d \<close> assms by auto
        then show False using \<open>c = d\<close> assms(9) by auto
     qed
  qed
qed




(*  ---------------------------  *)
(* |   Problem 22 (1 point):   | *)
(*  ---------------------------  *)
(* 1 point: 
 Formalise the following axiom: 
   if a point p lies outside of line l then there 
   must exist at least one line m that passes through p, 
   which does not intersect l *)
locale Non_Projective_Geometry = 
  Simple_Geometry +
  assumes parallels_Ex:
"\<forall>p \<in> plane. \<forall>l \<in> lines. p \<notin> l \<longrightarrow> (\<exists>m \<in> lines. p \<in> m \<and> m \<inter> l = {} )"

 (*  FILL THIS SPACE  *)
  

(*  ----------------------------  *)
(* |   Problem 23 (2 marks):   | *)
(*  ----------------------------  *)
(* Give a model of Non-Projective Geometry with cardinality 4. 
   Show that it is indeed a model using the command "interpretation" *)



definition "plane_4 \<equiv> {1::nat,2,3,4} "
definition "lines_4 \<equiv> {{1,2},{2,3},{1,3},{1,4},{2,4},{3,4}}"
interpretation Non_projective_geometry_card_4: 
  Non_Projective_Geometry plane_4 lines_4
  apply standard
       apply (simp add: plane_4_def lines_4_def)+
  done
   


 (*  FILL THIS SPACE  *)


(*  ----------------------------  *)
(* |   Problem 24 (3 marks):   | *)
(*  ----------------------------  *)
(*  Formalise and prove: 
     "it is not true that every pair of lines intersect"  *)
lemma (in Non_Projective_Geometry) non_projective: 
"\<exists>r \<in> lines. \<exists>s \<in> lines. r \<inter> s = {}"
proof -
  obtain "l1" where 1:"l1 \<in> lines" using one_line_exists by auto
  then obtain "q1" where 2: "q1 \<in> plane \<and> q1 \<notin> l1" using A5 by auto
  then  obtain " q1 \<notin> l1 \<longrightarrow> (\<exists>m \<in> lines. q1 \<in> m \<and> m \<inter> l1 = {} )" 
    using   1 parallels_Ex by simp
   then obtain "m1" where "m1 \<in> lines \<and> q1 \<in> m1 \<and> m1 \<inter> l1 = {}"
    using 2 by auto
  thus ?thesis using  1 by auto
qed


   (*  fill this space *)
   

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
  
(* GIVEN *)
locale Projective_Geometry = 
  Simple_Geometry + 
  assumes A6: "\<forall>l \<in> lines. \<forall>m \<in> lines. \<exists>p \<in> plane. p \<in> l \<and> p \<in> m"
      and A7: "\<forall>l \<in> lines.\<exists>x. card x = 3 \<and> x \<subseteq> l" 
  

(*  ----------------------------  *)
(* |   Problem 25 (3 marks):   | *)
(*  ----------------------------  *)
(*   Prove this alternative to axiom A7   *)
lemma (in Projective_Geometry) A7': 
  "\<forall>l \<in> lines. \<exists>p1 p2 p3. {p1,p2,p3} \<subseteq> plane \<and> distinct [p1,p2,p3] \<and> {p1,p2,p3} \<subseteq> l" 
proof
  fix l
  assume 1:"l \<in> lines"
  show "\<exists>p1 p2 p3. {p1, p2, p3} \<subseteq> plane \<and> distinct [p1, p2, p3] \<and> {p1,p2, p3} \<subseteq> l "
  proof -
    obtain x where 2:"card x = 3 \<and> x \<subseteq> l"  using 1 A7 by auto
    then have 3:"card x = 3" by (rule conjE)
    have "\<exists> p1 p2 p3. distinct [p1,p2,p3] \<and> x = {p1,p2,p3}" using 3
      by (rule construct_set_of_card3)
    then obtain "p1" "p2" "p3" where 4:"distinct [p1,p2,p3] \<and> x =
      {p1,p2,p3}" by auto
     obtain "l \<subseteq> plane \<and> l \<noteq> {}" using 1 A2  by auto
    then have 
"{p1,p2,p3} \<subseteq> plane \<and> distinct [p1,p2,p3] \<and> {p1,p2,p3} \<subseteq> l"
      using 4 2 by auto
    then show ?thesis by auto
  qed
qed


   



(*  ----------------------------  *)
(* |   Problem 26 (3 marks):   | *)
(*  ----------------------------  *)
(* Prove yet another alternative to axiom A7  *)

lemma (in Projective_Geometry) A7'': 
 "l \<in> lines \<Longrightarrow> {p,q} \<subseteq> l \<Longrightarrow> (\<exists>r \<in> plane. r \<notin> {p,q} \<and> r \<in> l)"
  oops

(*  ----------------------------  *)
(* |   Problem 27 (5 marks):   | *)
(*  ----------------------------  *)
lemma (in Projective_Geometry) two_lines_per_point:
  "\<forall>p \<in> plane. \<exists>l \<in> lines. \<exists>m \<in> lines. l \<noteq> m \<and> p \<in> l \<inter> m" 
proof 
  fix p 
  assume 1:"p \<in> plane"
  show " \<exists>l \<in> lines. \<exists>m \<in> lines. l \<noteq> m \<and> p \<in> l \<inter> m" 
  proof - 
    obtain "q" where "q \<in> plane" using A1 by auto
    then obtain "l" where 2:"l \<in> lines \<and> {p,q} \<subseteq> l " using A3 1 by auto
    then obtain "r" where 3:" r \<notin> l \<and> r \<in> plane" using A5 by auto
    then obtain "m" where 4: " m \<in> lines \<and> {p,r} \<subseteq> m " using A3 1  by auto
    then have 5:"l \<noteq> m" using  3 by auto
    have "p \<in> l \<inter> m" using 2 4 by auto
    then have "l \<noteq> m \<and> p \<in> l \<inter> m" using 5 by auto
    thus ?thesis using 2 4 by auto
  qed
qed







(*  ----------------------------  *)
(* |   Problem 28 (4 marks):   | *)
(*  ----------------------------  *)
lemma (in Projective_Geometry) external_line: 
  "\<forall>p \<in> plane. \<exists>l \<in> lines. p \<notin> l" 
proof 
  fix p 
  assume 1:"p \<in> plane" 
  show "\<exists>l \<in> lines. p \<notin> l"
  proof - 
     obtain "q" where 4:"q \<in> plane" using A1 by auto
    then obtain "l" where 2:"l \<in> lines \<and> {p,q} \<subseteq> l " using A3 1 by auto
    then obtain "r" where 3:" r \<notin> l \<and> r \<in> plane" using A5 by auto
    then obtain "m" where 6:"m \<in> lines \<and> {q,r} \<subseteq> m" using A3 4 by auto
    then have 7:"m \<noteq> l" using 3 by auto
    then obtain " l \<inter> m = {} \<or> (\<exists>q\<in>plane. l \<inter> m = {q})" using A4 2 6 by
        auto
    have "p \<notin> m"
    proof
      assume 5:"p \<in> m"
      obtain  " l \<inter> m = {} \<or> (\<exists>q\<in>plane. l \<inter> m = {q})" using A4 2 6 7 by
        auto
      then  show False 
      proof (rule disjE)
        assume 8:"l \<inter> m = {}"
        have 9:"{p,q,r} \<subseteq> m" using 5 6 by auto
        then show False using 2 8  by auto
      next
        assume " \<exists>q\<in>plane. l \<inter> m = {q}"
        then obtain "t" where 10:"l \<inter> m = {t}" by auto
        have 9:"{p,q,r} \<subseteq> m" using 5 6 by auto
        then have "{p,q} \<subseteq> {t}" using 2 10  by auto
        thus False 
          oops

       





(*  ----------------------------  *)
(* |   Problem 29 (6 marks):   | *)
(*  ----------------------------  *)
lemma (in Projective_Geometry) three_lines_per_point:
  "\<forall>p \<in> plane. \<exists>l m n. distinct [l,m,n] \<and> {l,m,n} \<subseteq> lines \<and> p \<in> l \<inter> m \<inter> n" 
  oops


(*  -----------------------------  *)
(* |   Problem 30 (8 marks):   | *)
(*  -----------------------------  *)
lemma (in Projective_Geometry) at_least_seven_points: 
  "\<exists>p1 p2 p3 p4 p5 p6 p7. distinct [p1,p2,p3,p4,p5,p6,p7] \<and> {p1,p2,p3,p4,p5,p6,p7} \<subseteq> plane" 
  oops

  
(*  -----------------------------  *)
(* |   Problem 31 (3 marks):    | *)
(*  -----------------------------  *)
(*  Give a model of Projective Geometry with 7 points; use the 
    command "interpretation" to prove that it is indeed a model. *)

 (*  FILL THIS BLANK *)


end
