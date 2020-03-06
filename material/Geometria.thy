theory Geometria
imports Main 
begin

(*  --------------------------------------------------------------  *)
(* |                            PART 3:                           | *)
(* |                   FORMALISING AND REASONING                  | *)
(* |                ABOUT GEOMETRIES USING LOCALES                | *)
(*  --------------------------------------------------------------  *)

(*  From this point on you can also use metis and meson, but not smt.   *)

(*  ----------------------------  *)
(* |   Problem 14 (2 marks):   | *)
(*  ----------------------------  *)
(* State formally the following axioms 
   (first 3 are given; one point per each of the others): *)
locale Simple_Geometry =
  fixes plane :: "'a set"
  fixes lines :: "('a set) set"
  assumes A1: "plane \<noteq> {}"
      and A2: "\<forall>l \<in> lines. l \<subseteq> plane \<and> l \<noteq> {}"
      and A3: "\<forall>p \<in> plane. \<forall>q \<in> plane. \<exists>l \<in> lines. {p,q} \<subseteq> l"
      and A4: "\<forall>l \<in> lines. \<forall>r \<in> lines. l \<noteq> r \<Longrightarrow>
               l \<inter> r = {} \<or> (\<exists>q \<in> plane. l \<inter> r = {q}) "
               (* Two different lines intersect in no more than one 
                  point. *)
              \<comment> \<open><Pendiente de corregir A4\<close>
      and A5: "\<forall>l \<in> lines. \<exists>q \<in> plane. q \<notin> l"
              (* For every line L there is a point in the plane outside 
                 of L. *)

(*  ---------------------------  *)
(* |   Problem 15 (1 point):   | *)
(*  ---------------------------  *)
(* Formalise the statement: the set of lines is non-empty *)
lemma (in Simple_Geometry) one_line_exists: 
  "\<exists>l \<in> lines. l \<subseteq> plane " 
  using A1 A2 A3 by auto 
  (* FILL THIS SPACE: The set of lines is non-empty *)

(*  ----------------------------  *)
(* |   Problem 16 (2 marks):   | *)
(*  ----------------------------  *)
lemma (in Simple_Geometry) two_points_exist: 
  "\<exists>p1 p2. p1 \<noteq> p2 \<and> {p1,p2} \<subseteq> plane"
  by (metis A2 A3 A5 bot.extremum_uniqueI one_line_exists subsetD subset_emptyI subset_trans)


(*  ----------------------------  *)
(* |   Problem 17 (3 marks):   | *)
(*  ----------------------------  *)
lemma (in Simple_Geometry) three_points_exist: 
  "\<exists>p1 p2 p3. distinct [p1,p2,p3] \<and> {p1,p2,p3} \<subseteq> plane" 
proof - 
  have "\<exists>p1 p2. p1 \<noteq> p2 \<and> {p1,p2} \<subseteq> plane" by (rule two_points_exist)
  then obtain "p1" where  "\<exists>p2. p1 \<noteq> p2 \<and> {p1,p2} \<subseteq> plane" by (rule exE) 
  then obtain "p2" where 1:" p1 \<noteq> p2 \<and> {p1,p2} \<subseteq> plane" by (rule exE) 
  then have 7:"p1 \<noteq> p2" by (rule conjE) 
  have 3:"{p1,p2} \<subseteq> plane "  using 1 by (rule conjE)
  then have 2:"p1 \<in> plane" by simp
  have "p2 \<in> plane" using 3 by simp
  have  "\<forall>p \<in> plane. \<forall>q \<in> plane. \<exists>l \<in> lines. {p,q} \<subseteq> l" using A3 by simp
  then obtain "\<forall>q \<in> plane. \<exists>l \<in> lines. {p1,q} \<subseteq> l" using 2 by simp
  then obtain " \<exists>l \<in> lines. {p1,p2} \<subseteq> l" using 3 by simp 
  then obtain "l1" where 5:"l1 \<in> lines \<and> {p1,p2} \<subseteq> l1" by auto
  have "\<forall>l \<in> lines. \<exists>q \<in> plane. q \<notin> l" using A5 by simp
  then obtain "\<exists>q \<in> plane . q \<notin> l1" using 5 by simp
  then obtain "p3" where 6:"p3 \<in> plane \<and> p3 \<notin> l1" by auto
  have "p1 \<in> l1" using 5 by auto
  then have "p1 \<noteq> p3" using 5 6 by auto
  then have 8: " distinct [p1,p2,p3]" using 7 5 6 by auto
  have 9: "{p1,p2,p3} \<subseteq> plane" using 6 3 by auto
  show ?thesis using 8 9 by auto
qed



(*  ----------------------------  *)
(* |   Problem 18 (3 marks):   | *)
(*  ----------------------------  *)
(* REMEMVER THAT CARD OF INFINITE SETS IS 0! *)
lemma (in Simple_Geometry) card_of_plane_greater: 
  "finite plane \<Longrightarrow> card plane \<ge> 3"
  oops

(*  ----------------------------  *)
(* |   Problem 19 (2 marks):   | *)
(*  ----------------------------  *)
(* GIVE THE SMALLEST MODEL! *)
definition "plane_3 \<equiv>  "
definition "lines_3 \<equiv> (* FILL THIS SPACE *)"
interpretation Simple_Geometry_smallest_model: 
  Simple_Geometry plane_3 lines_3
  apply standard 
  oops
      

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
  oops


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
  oops


(*  ---------------------------  *)
(* |   Problem 22 (1 point):   | *)
(*  ---------------------------  *)
(* 1 point: 
 Formalise the following axiom: 
   if a point p lies outside of a line l then there 
   must exist at least one line m that passes through p, 
   which does not intersect l *)
locale Non_Projective_Geometry = 
  Simple_Geometry +
  assumes parallels_Ex: (*  FILL THIS SPACE  *)
  

(*  ----------------------------  *)
(* |   Problem 23 (2 marks):   | *)
(*  ----------------------------  *)
(* Give a model of Non-Projective Geometry with cardinality 4. 
   Show that it is indeed a model using the command "interpretation" *)

 (*  FILL THIS SPACE  *)


(*  ----------------------------  *)
(* |   Problem 24 (3 marks):   | *)
(*  ----------------------------  *)
(*  Formalise and prove: 
     "it is not true that every pair of lines intersect"  *)
lemma (in Non_Projective_Geometry) non_projective: 
   (*  fill this space *)
   oops

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
      and A7: "\<forall>l \<in> lines. \<exists>x. card x = 3 \<and> x \<subseteq> l"
  

(*  ----------------------------  *)
(* |   Problem 25 (3 marks):   | *)
(*  ----------------------------  *)
(*   Prove this alternative to axiom A7   *)
lemma (in Projective_Geometry) A7': 
  "\<forall>l \<in> lines. \<exists>p1 p2 p3. {p1,p2,p3} \<subseteq> plane \<and> distinct [p1,p2,p3] \<and> {p1,p2,p3} \<subseteq> l" 
  oops


(*  ----------------------------  *)
(* |   Problem 26 (3 marks):   | *)
(*  ----------------------------  *)
(* Prove yet another alternative to axiom A7  *)
lemma (in Projective_Geometry) A7'': 
  "l \<in> lines \<Longrightarrow> {p,q} \<subseteq> l  \<Longrightarrow> (\<exists>r \<in> plane. r \<notin> {p,q} \<and> r \<in> l)"
  oops


(*  ----------------------------  *)
(* |   Problem 27 (5 marks):   | *)
(*  ----------------------------  *)
lemma (in Projective_Geometry) two_lines_per_point:
  "\<forall>p \<in> plane. \<exists>l \<in> lines. \<exists>m \<in> lines. l \<noteq> m \<and> p \<in> l \<inter> m" 
  oops


(*  ----------------------------  *)
(* |   Problem 28 (4 marks):   | *)
(*  ----------------------------  *)
lemma (in Projective_Geometry) external_line: 
  "\<forall>p \<in> plane. \<exists>l \<in> lines. p \<notin> l" 
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
