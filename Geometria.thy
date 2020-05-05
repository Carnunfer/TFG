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

También de cada tipo de geometría se dará el modelo mínimo que posee
 cada una, esto se hará mediante el comando \textbf{interpretation}.
El comando \textbf{interpretation} como su nombre indica consiste en
 interpretar los comandos locales, es decir, dar un modelo(que en este
 caso será el mínimo que ofrece cada entorno local) y probar todos los
 axiomas que este tenga.


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

text \<open>
A continuación vamos a presentar una serie de lemas que vamos a
 demostrar dentro del entorno de geometría simple.

El primer lema es el siguiente:

\begin{lema}\label{one-line-exists}
Existe al menos una línea.
\end{lema}

\begin{demostracion}
Vamos a demostrar que el conjunto de línes es no vacío, para ello,
 supongamos en primer lugar por el axioma A1 que $\exists q$ tal que $q$
pertenece al plano. Entonces por el axioma A2 tenemos que $\exists l$
 línea tal que el conjunto $\{q,q\} \subseteq l$ luego ya tenemos
 probado que existe una línea.
\end{demostracion}

La formalización del lema y su demostración en Isabelle/HOl es la siguiente:

\<close>
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

text \<open>
El segundo lema es el siguiente 

\begin{lema}
Existen al menos dos puntos que son diferentes en el plano 
\end{lema}

\begin{demostracion}
Para la demostración del lema, vamos a usar el lema anterior, luego
 supongamos que $\exists l$ tal que $l$ es una línea. Luego por el
 axioma A2, sabemos que $l \neq \emptyset$ luego esto implica que
 $\exists q$ tal que $q \in l.$ Por otro lado por el axioma A5 sabemos
 que $\exists p$ tal que es un punto y $p \notin l$ luego ya tenemos
 probada la existencia de dos puntos. A parte, como $p \notin l$ y $q
 \in l$ tienen que ser distintos. 
\end{demostracion}

La especificación y demostración del lema en Isabelle/HOL es la siguiente:
\<close>
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
text \<open>
El siguiente lema es el siguiente: 

\begin{lema}
Existen al menos tres puntos diferentes en el plano.
\end{lema}

\begin{demostracion}
Para la demostración del lema vamos a usar el lema anterior, es decir,
supongamos que $\exists p,q$ tal que $p \neq q.$ Por el axioma A2 se
 tiene que $\exists l$ línea con ${p,q} \subseteq {l}.$ Usando el axioma
A5 obtenemos que $\exists r$ tal que $r \notin l,$ luego ya hemos 
probado la existencia. Veamos que son diferentes, es decir, como hemos
 tomado $p \neq q$ simplemente tenemos que probar que $r \neq q$ y $r
 \neq p$. Como $r \notin l$ ya se tiene probado.
\end{demostracion}


La especificación y demostración del lema en Isabelle/HOL es la siguiente:
\<close>
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
text \<open>
El siguiente lema es una consecuencia inmediata del lema anterior.

\begin{lema}
Si el plano es finito, entonces la cardinalidad del plano es mayor o 
igual que $3.$
\end{lema}

\begin{demostracion}
Usando el lema anterior, ya tenemos probado que $\exists p,q,r$
 pertenecientes al plano  con $p  \neq q \neq r.$ Como estos puntos son
 diferentes se tiene directamente que al meno la cardinalidad del plano
 es mayor o igual que $3.$
\end{demostracion}

La especificación y demostración del lema en Isabelle/HOL es la siguiente:
\<close>
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

(* ---------------------------------------------------------------------
   Problem 20
   ------------------------------------------------------------------ *)
text \<open>
El siguiente lema es el siguiente:

\begin{lema}
Sea $l$ una línea tal que existen dos puntos $\{a,b\} \subseteq l$ con
 $a \neq b,$  un punto $p$ tal que $p \notin l.$ Sea $n$ una línea tal que
$\{a,p\} \subseteq n$ y $m$ otra línea tal que $\{b,p\} \subseteq m.$
 Entonces $m \neq n.$ 
\end{lema}

\begin{demostracion}
La demostración se hará por reducción al absurdo, es decir, supongamos
 que $m = n$ y se llegará a un absurdo. Primero notemos que $m \neq l$
 ya que $p \notin l$ pero $p \in m,$ luego podemos aplicar el axioma A4
 a las líneas $m$ y $l.$ Al aplicarlo resulta que tenemos que $l \cap m
 = \emptyset$ o existe un punto $q$ tal que $l \cap m = \{q\}.$ 

Primero supongamos que $l \cap m = \emptyset,$ sin embargo $b \in l$ y
 $b \in m$ luego hemos llegado a n absurdo.

Segundo supongamos que sea $q$ el punto tal que $l \cap m = {q},$ sin
 embargo al principio se ha supuesto que $m = n$. Por lo tanto, se tiene
que $\{a,b\} \subseteq \{q\}$ con lo que se ha llegado a un absurdo ya que $a \neq
b.$

Por los dos casos se ha llegado a un absurdo luego, $m \neq n.$
\end{demostracion}

Para tener una visión geométrica de la demostración incluimos la figura
 \ref{lineas_diferentes}.


\begin{figure}[H]
\centering
\includegraphics[height=6cm]{geogebra.png}
\caption{Visión geométrica de la demostración de líneas diferentes}
\label{lineas_diferentes}
\end{figure}

La especificación y demostración del lema en Isabelle/HOL es la siguiente:
\<close>

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
text \<open>El siguiente lema es: 

\begin{lema}
Sea $l$ una línea tal que existen dos puntos $\{a,b\} \subseteq l$ con
 $a \neq b,$  un punto $p$ tal que $p \notin l.$ Sea $n$ una línea tal que
$\{a,p\} \subseteq n$ y $m$ otra línea tal que $\{b,p\} \subseteq m.$
Supongamos además que existen otros dos puntos $c,d$ tales que
 pertenecen a $n$ y $m$ respectivamente y $c \neq p.$ Entonces $c \neq
 d.$
\end{lema}

\begin{demostracion}
La demostración se hará por reducción al absurdo, es decir, supongamos
 que $c = d$ y llegaremos a una contradicción. Tenemos todas las
 hipótesis del lema anterior, luego $m \neq n,$ por lo que podemos
 aplicar el axioma A4 a las líneas $m$ y $n.$ Se tiene por lo tanto que
 $m \cap n = \emptyset$ o existe un punto $q$ tal que $m \cap n = \{q\}.$

Primero supongamos que $m \cap n = \emptyset,$ sin embargo por hipótesis
se tiene que $p \in m$ y $p \in n$ luego hemos llegado a una
 contradicción.

Segundo sea $q$ el punto tal que $m \cap n = \{q\}.$ Como se ha supuesto
que $c = d$ se tiene que ${c,p} \subseteq \{q\},$ pero por hipótesis se
 tiene que $c \neq p$ luego se ha llegado a una contradicción.

En los dos caso se ha llegado a una contradicción, por lo que $c \neq d.$
\end{demostracion}

Para entender mejor la demostración se puede ver geométricamente en la 
siguiente figura \ref{puntos_diferentes}


\begin{figure}[H]
\centering
\includegraphics[height=6cm]{geogebra2.png}
\caption{Visión geométrica de la demostración de puntos diferentes}
\label{puntos_diferentes}
\end{figure}

La especificación y demostración del lema en Isabelle/HOL es la siguiente:
\<close>
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


subsection \<open>
Interpretación mínimo modelo geometría simple 
\<close>

text \<open>
El mínimo modelo que tiene la geometría simple es considerar el plano
 como el conjunto formado por tres números $\{a,b,c\}$, ya pueden ser
 enteros,naturales etc y con ellos formar únicamente 3 líneas. En este
 caso serían las combinaciones que se pueden hacer de 2 elementos de
 un conjunto de 2, es decir, 3. 

Para ello se va a dar el la definicion del \textbf{planes-3} que es el
 plano de 3 elementos y \textbf{lines-3} que es el conjunto formado por
 3 líneas.
\<close>
definition "plane_3 \<equiv> {1::nat,2,3} "

definition "lines_3 \<equiv> {{1,2},{2,3},{1,3}}"

interpretation Simple_Geometry_smallest_model:
  Simple_Geometry plane_3 lines_3
  apply standard 
      apply (simp add: plane_3_def lines_3_def)+
  done


section \<open>Geometría no proyectiva \<close>

(* ---------------------------------------------------------------------
   Problem 22: Formalise the following axiom: 
     if a point p lies outside of line l then there must exist at least
     one line m that passes through p, which does not intersect l 
  ------------------------------------------------------------------- *)
subsection \<open>Entorno local \<close>

text \<open>
La geometría no proyectiva es un tipo de geometría en el que asusmimos
 paralelismo, en nuestro caso entre rectas.

\begin{definicion}
El paralelismos es una relación que se establece entre dos rectas
cualesquiera del plano, esta relación dice que dos rectas son paralelas
 si bien son la misma recta o no comparten ningún punto, es decir, su
 intersección es vacía.
 \end{definicion}

Gracias a esta relación entre rectas, podemos definir un nuevo entorno
 local añadiendo al ya definido \textbf{Simple-Geometry} un nuevo
 axioma, el axioma de la existencia del paralelismo.


\textbf{Parallels-Ex}: sea $p$ un punto del plano y $l$ una línea. Si $p
\notin l$ entonces debe existir una línea $m$ tal que $p \in m$ y $l
 \cap m = \emptyset.$

Al nuevo entorno local lo denotaremos como
 \textbf{Non-Projective-Geometry}.
\<close>
locale Non_Projective_Geometry =
  Simple_Geometry +
  assumes parallels_Ex:
    "\<forall>p \<in> plane. \<forall>l \<in> lines. p \<notin> l \<longrightarrow> (\<exists>m \<in> lines. p \<in> m \<and> m \<inter> l = {} )"

(* ---------------------------- ----------------------------------------
   Problem 23: Give a model of Non-Projective Geometry with 
   cardinality 4. 
   Show that it is indeed a model using the command "interpretation" 
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Problem 24: Formalise and prove: 
     "it is not true that every pair of lines intersect"  
  ------------------------------------------------------------------- *)

subsection \<open>Proposiciones de geometría no proyectiva \<close>

text\<open>
A continuación vamos a presentar un lema sobre geometría no proyectiva:

\begin{lema}
Es falso que todo par de líneas intersecta en un punto.
\end{lema}

\begin{demostracion}
La demostración se hará suponiendo que es cierto y llegaremos a una
 contradicción, es decir, supongamos que se verifica que $\forall \,l\, m$
 líneas se tiene que $l \cap m \neq \emptyset.$ \\
Sea ahora una línea, denostemosla $l1$, obtenida por el el lema
 \ref{one-line-exists}. Luego por el axioma A5 obtenemos un punto $q1$
 tal que $q1 \notin l1$, usando el axioma \textbf{Parallels-Ex} aplicado
al punto $q1$ y a la línea $l1$ obtenemos que existe una línea $m$ tal
 que $q1 \in m$ y $m \cap l = \emptyset.$ Por lo tanto, hemos llegado a
 una contradicción ya que se ha demostrado que existen dos líneas cuya
 intersección es vacía.
\end{demostracion}


La formalización y demostración en Isabelle/Hol es la siguiente:
\<close>
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



subsection \<open>Interpretacion modelo geometría no proyectiva \<close>

text \<open>
El mínimo modelo de la geometría no proyectiva es considerar que el
 plano tiene 4 elementos, es decir, considerar el plano como
 $\{a,b,c,d\}$ siendo estos números enteros,naturales etc. Con estos 4
 elementos para que sea un modelo de la geometría no proyectiva hay que
 formar como mínimo 6 rectas.

Para ello vamos a dar la definicion \textbf{plane-4} que es el plano
 formado por 4 elementos y \textbf{lines-4} que son las líneas asociadas
a estos elementos.
\<close>
definition "plane_4 \<equiv> {1::nat, 2, 3, 4}"

definition "lines_4 \<equiv> {{1,2},{2,3},{1,3},{1,4},{2,4},{3,4}}"

interpretation Non_projective_geometry_card_4:
  Non_Projective_Geometry plane_4 lines_4
  apply standard
       apply (simp add: plane_4_def lines_4_def)+
  done

(* The following are some auxiliary lemmas that may be useful.
   You don't need to use them if you don't want. *)



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

lemma construct_set_of_card3:
  "card x = 3 \<Longrightarrow> \<exists> p1 p2 p3. distinct [p1,p2,p3] \<and> x = {p1,p2,p3}" 
  by (metis card_eq_SucD distinct.simps(2) 
      distinct_singleton list.set(1) list.set(2) numeral_3_eq_3)

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


lemma (in Projective_Geometry) punto_no_pertenece:
  assumes "l2 \<in> lines \<and> {p,r} \<subseteq> l2"
          "l \<in> lines \<and>  {r,s} \<subseteq> l"
          "p \<noteq> r"
          "s \<notin> l2"
        shows "p \<notin> l"
proof 
  assume 1:"p \<in> l"
  have "l \<inter> l2 = {} \<or> (\<exists>q \<in> plane. l \<inter> l2 = {q})" using A4
        assms(1,2,4)  by auto
    then show False 
    proof 
      assume "l \<inter> l2 = {}"
      then show False using assms(1,2) by auto
    next 
      assume " \<exists>q\<in>plane. l \<inter> l2 = {q}"
      then obtain "t" where "l \<inter> l2 = {t}" by auto
      then have "{p,r} \<subseteq> {t}" 
          using  assms(1,2) 1  by auto
      then show False 
        using assms(3)  by auto
    qed
  qed


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
    obtain l2 where 4: "l2 \<in> lines \<and> {p,r} \<subseteq> l2" 
      using 1 3 A3 by auto
    then obtain s where 5: "s \<in> plane \<and> s \<notin> l2" 
      using A5 3 by auto
    obtain l where 6: "l \<in> lines \<and> {r,s} \<subseteq> l" 
      using 3 5 A3 by auto
    have "p \<noteq> r" using 2 3 by auto
    then have "p \<notin> l" 
      using 4 6 5 punto_no_pertenece [of l2 p r l s] by simp
    then show ?thesis 
      using 6 by auto
  qed
qed

(* --------------------------------------------------------------------
   Problem 29   
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) lineas_distintas:
  assumes "m \<in> lines \<and> {b,p} \<subseteq> m"
          "n \<in> lines \<and> {c,p} \<subseteq> n"
          "h \<in> lines \<and> {a,b,c} \<subseteq> h"
          "h \<noteq> m" 
          "b \<noteq> c"
        shows "m \<noteq> n"
proof 
  assume  1:"m = n" 
  show False
  proof - 
    have  "{c,p,b} \<subseteq> m" 
      using assms(1,2) 1 by auto
    have "m \<inter> h = {} \<or> (\<exists>q\<in>plane. m \<inter> h = {q})" 
      using A4 assms(1,3,4) by auto
    then show False
    proof 
      assume "m \<inter> h = {}" 
      then show False 
        using assms(1,3) by auto
    next 
      assume "\<exists>q\<in>plane. m \<inter> h = {q}"
      then obtain t where "t \<in> plane \<and> m \<inter> h = {t}" 
        by auto
      then have "{c,b} \<subseteq> {t}" 
        using assms(1,2,3) 1 by auto
      then show False 
        using assms(5) by auto
    qed
  qed
qed

lemma (in Projective_Geometry) three_lines_per_point:
  "\<forall>p \<in> plane. \<exists>l m n. 
    distinct [l,m,n] \<and> {l,m,n} \<subseteq> lines \<and> p \<in> l \<inter> m \<inter> n" 
proof 
  fix p 
  assume 1: "p \<in> plane"
  show "\<exists>l m n. distinct [l,m,n] \<and> {l,m,n} \<subseteq> lines \<and> p \<in> l \<inter> m \<inter> n"
  proof - 
    obtain h where 2: "h \<in> lines \<and> p \<notin> h" 
      using 1 external_line by auto
    then obtain a b c 
      where 3: "{a,b,c} \<subseteq> plane \<and> distinct [a,b,c] \<and> {a,b,c} \<subseteq> h"
      using A7a by auto  
    then obtain l where 4: "l \<in> lines \<and> {a,p} \<subseteq> l" 
      using 1 A3 by auto
    obtain m  where 5: "m \<in> lines \<and> {b,p} \<subseteq> m" 
      using 1 3 A3 by auto
    obtain n where 6: "n \<in> lines \<and> {c,p} \<subseteq> n" 
      using 1 3 A3 by auto
    have 7:"h \<noteq> l" 
      using 4 2 by auto
    have "a \<noteq> b" 
      using 3 by auto
    then have 9: "m \<noteq> l" 
      using 3 4 5 2 7 lineas_distintas [of l a p m b h c] by simp
    have 8: "h \<noteq> m" 
      using 5 2 by auto
    have  "b \<noteq> c" 
      using 3 by auto
    then have 10: "m \<noteq> n" 
      using 6 5 3 2 8 lineas_distintas [of m b p n c h a] by simp
    have "a \<noteq> c" 
      using 3 by auto
    then  have 11: "l \<noteq> n" 
      using 2 3 4 6 7 lineas_distintas [of l a p n c h b] by simp 
    show ?thesis 
      using  4 5 6 9 10 11 by auto
  qed
qed

(* ---------------------------------------------------------------------
   Problem 30
   ------------------------------------------------------------------ *)

lemma (in Projective_Geometry) puntos_diferentes:
  assumes "l \<in> lines"
          "l1 \<in> lines"
          "{p,c} \<subseteq> l"
          "{q,c} \<subseteq> l1"
          "l \<noteq> l1"
          "c \<noteq> p"
        shows "p \<noteq> q" 
proof 
  assume 1: "p = q" 
  have "l \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l \<inter> l1 = {q})" 
    using assms(1,2,5) A4 by auto
  then show False
  proof 
    assume "l \<inter> l1 = {}"
    then show False 
      using assms(3,4) by auto
  next
    assume "\<exists>q\<in>plane. l \<inter> l1 = {q}"
    then obtain t where "l \<inter> l1 = {t}" 
      by auto
    then have "{p,c} \<subseteq> {t}" 
      using assms(3,4) 1 by auto
    then show False 
      using assms(6) by auto
  qed
qed

lemma (in Projective_Geometry) lineas_diferentes_2:
  assumes "l \<in> lines \<and> {p,r} \<subseteq> l"
          "l1 \<in> lines \<and> {p,q} \<subseteq> l1"
          "l2 \<in> lines \<and> {r,q} \<subseteq> l2"
          "l1 \<noteq> l "
          "p \<noteq> r"
  shows   "l1 \<noteq> l2"
proof 
  assume 1:"l1 = l2"
  have "l \<inter> l1 = {} \<or> (\<exists>q \<in> plane. l \<inter> l1 = {q})"
    using A4 assms(1,2,4) by auto
  then show False 
  proof 
    assume "l \<inter> l1 = {}"
    then show False 
      using assms(1,2) by auto
  next
    assume "\<exists>q\<in>plane. l \<inter> l1 = {q}"
    then obtain t where "l \<inter> l1 = {t}" by auto
    then have "{p,r} \<subseteq> {t}" 
      using assms(1,2,3) 1 by auto
    then show False 
      using assms(5) by auto
  qed
qed

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
    using construct_set_of_card3 [of x] by auto
  then have 4: "{p1,p2,p3} \<subseteq> l" 
    using 2 by auto
  then have 5: "{p1,p2,p3} \<subseteq> plane" 
    using A2 1 by auto
  obtain q where 6: "q \<in> plane \<and> q \<notin> l"
    using A5 1 by auto
  then have 7: "distinct [p1,p2,p3,q]" 
    using 3 4 by auto
  obtain l1 where 8: "l1 \<in> lines \<and> {p1,q} \<subseteq> l1" 
    using 5 6 A3 by auto
  then have 9: "l1 \<noteq> l" 
    using 6 by auto
  obtain p4 where 10: "p4 \<notin> {p1,q} \<and> p4 \<in> l1" 
    using A7b [of l1 p1 q] 8 by auto
  have 11: "p4 \<noteq> p2" 
    using 3 4 1 6 2 10 8 puntos_diferentes [of l1 l p4 p1 p2] by auto
  have 12: "p4 \<noteq> p3" 
    using 7 1 9 4 10 8 puntos_diferentes [of l1 l p4 p1 p3] by auto
  obtain l2 where 13: "l2 \<in> lines \<and> {p2,q} \<subseteq> l2" 
    using 5 6 A3 by auto
  then obtain p5 where 14: "p5 \<notin> {p2,q} \<and> p5 \<in> l2" 
    using A7b [of l2 p2 q] 7 by auto
  have 15: "l2 \<noteq> l" 
    using 6 13 by auto
  have 16:"p5 \<noteq> p1" using 1 13 14 4  15 
 puntos_diferentes [of l l2 p1 p2  p5] by auto 
  have 17:"p5 \<noteq> p3" using 1 13 14 4  15
 puntos_diferentes [of l l2 p3 p2 p5] 
    by auto
  have 20:"l1 \<noteq> l2 " using 1 9 13 4 8 7  
      lineas_diferentes_2 [of l p1 p2 l1 q l2 ] by simp
  have 21: "p4 \<noteq> p5" using 13 8 14 4 10 20 
      puntos_diferentes [of l1 l2 p4 q p5]  by auto
  obtain l3 where 22: "l3 \<in> lines \<and> {p3,q} \<subseteq> l3" 
    using A3 5 6 by auto
  then obtain p6 where 23: "p6 \<notin> {p3,q} \<and> p6 \<in> l3" 
    using A7b by metis
  have 25: "p6 \<noteq> p1" using 1 22 6 4  23 
puntos_diferentes [of l3 l p1 p3 p6]  by auto 
  have 26: "p6 \<noteq> p2" using 1 22 6 23 4 
 puntos_diferentes [of l3 l p2 p3 p6] by auto
  have 29:"l1 \<noteq> l3" using  1 4 9 22 8 7
 lineas_diferentes_2  [of l p1 p3 l1 q l3]  by simp
  have 31:"p6 \<noteq> p4" using 22 8 10 23  29  
puntos_diferentes [of l1 l3 p4 q p6] by auto
  have 34:"l2 \<noteq> l3" using 1 4 13 22 15 7 
lineas_diferentes_2  [of l p2 p3 l2 q l3] by simp
  have 35:"p6 \<noteq> p5" using  22 13 23 14 34 
 puntos_diferentes [of l2 l3 p5 q p6] by auto
  moreover have "distinct [p1,p2,p3,p4,p5,p6,q]" 
     using 7 10 11 12 14 16 17 21 23 25 26 31 7 35 by auto
  moreover have "{p1,p2,p3,p4,p5,p6,q} \<subseteq> plane" 
    using 6 5  A2 10 8 14 13 22 23 by auto
  ultimately show ?thesis  by metis
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

lemma aux3a: "card {3::nat, 4, 5} = 3"
  by auto

lemma aux3: "\<exists>x. card x = 3 \<and> x \<subseteq> {3::nat, 4, 5}"
  using aux3a by blast

lemma aux4a: "card {5::nat, 7, 2} = 3"
  by auto

lemma aux4: "\<exists>x. card x = 3 \<and> x \<subseteq> {5::nat, 7, 2}"
  using aux4a by blast

lemma aux5a: "card {3::nat, 7, 6} = 3"
  by auto

lemma aux5: "\<exists>x. card x = 3 \<and> x \<subseteq> {3::nat, 7, 6}"
  using aux5a by blast

lemma aux6a: "card {Suc 0, 4, 7} = 3"
  by auto

lemma aux6: "\<exists>x. card x = 3 \<and> x \<subseteq> {Suc 0, 4, 7}"
  using aux6a by blast

lemma aux7a: "card {2::nat, 4, 6} = 3"
  by auto

lemma aux7: "\<exists>x. card x = 3 \<and> x \<subseteq> {2::nat, 4, 6}"
  using aux7a by blast
interpretation Projective_Geometry_smallest_model:
  Projective_Geometry plane_7 lines_7
  apply standard 
        apply (simp add: plane_7_def lines_7_def)+
  apply (intro conjI)
  apply (rule aux1)
  apply (rule aux2)
  apply (rule aux3)
  apply (rule aux4)
  apply (rule aux5)
  apply (rule aux6)
  apply (rule aux7)
  done


end
