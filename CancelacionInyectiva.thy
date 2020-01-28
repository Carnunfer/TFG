(* Cancelación de funciones inyectivas *)

(*<*) 
theory CancelacionInyectiva
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

section \<open>Cancelación de funciones inyectivas\<close>
subsection \<open>Demostración en lenguaje natural \<close>

text \<open>\comentario{Añadir lemas usados al Soporte.}\<close>

text \<open>El siguiente teorema que se va a probar es una caracterización de
  las funciones inyectivas. Primero se definirá el significado de
  inyectividad de una función y la propiedad de ser cancelativa por la
  izquierda. 

  Una función $f : B \longrightarrow C$ es inyectiva si 
  $$\forall x,y \in \ B : f(x) = f(y) \Longrightarrow x = y.$$

  Una función $f : B \longrightarrow C$ es cancelativa por la izquierda
 si $$\forall A: (\forall g,h: A \longrightarrow B) : 
    f \circ g = f \circ h \Longrightarrow g = h.$$

  El teorema es el siguiente:
  \begin{teorema}
    La función $f$ es inyectiva, si y solo si, es cancelativa por la
 izquierda. 
  \end{teorema}

  Vamos a hacer dos lemas previos, ya que se  descompone la
  doble implicación en dos implicaciones y se va a  demostrar cada una
  de ellos por separado.

  \begin{lema}[Condición necesaria]
    Si $f$ es una función inyectiva, entonces f es cancelativa por la
 izquierda.
  \end {lema}

  \begin{demostracion}
  Vamos a probar  que $\forall x. \, g(x) = h(x).$
  Por hipótesis se tiene que 
$$f \circ g = f \circ h \Longrightarrow (f \circ g)(x) = (f
 \circ h)(x) \stackrel{def.}{\Longrightarrow} f(g(x)) = f(h(x))
 \stackrel{f \,  inyect.}{\Longrightarrow} g(x)=h(x)$$
  \end{demostracion}

  \begin {lema}[Condición suficiente] 
   Si f es cancelativa por la izquierda entonces f es inyectiva.
  \end {lema} 

  \begin {demostracion}
    Si el dominio de la función $f$ fuese vacío, f  es inyectiva.
    Supongamos que el dominio de la función $f$ es distinto del vacío y
    que f verifica la propiedad de ser cancelativa por la izquierda.
    Hay que demostrar que $\forall a,b$ tales que $f(a) = f(b)$, esto
    implica que $a = b$. 

    Sean $a,b$ tales que $f(a) = f(b)$. 

    Consideremos las funciones constantes $g(x) = a  \ \forall x$  y
    $h(x) = b \  \forall x.$
    Veamos que $f \circ g = f \circ h.$ En efecto, $\forall x$
    $$(f \circ g)(x) = f(g(x)) = f(a)$$
    $$(f \circ h)(x) = f(h(x)) = f(b)$$
    Por hipótesis se tiene que $f(a) = f(b)$ luego $f \circ g = f \circ
 h.$ Por hipótesis se tiene que $f$ es cancelativa por la izquierda, por
lo tanto, esto implica que
$$g = h \Longrightarrow g(x) = h(x) \, \forall x \Longrightarrow a =
 b.$$
\end{demostracion}
\<close>

subsection \<open>Especificación en Isabelle/Hol\<close>

text \<open>Su especificación es la siguiente, pero al igual que se ha  hecho
 en la demostración a mano se va a demostrar a través de dos lemas:\<close>

theorem caracterizacion_funcion_inyecctiva:
  "inj f \<longleftrightarrow> (\<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
  oops

text \<open>Los lemas asociados a cada implicación son los siguientes:\<close>

lemma "\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h) \<Longrightarrow> inj f"
  oops

lemma "inj f \<Longrightarrow> (\<forall>g h.(f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
  oops

text \<open>En la especificación anterior, @{term "inj f"} es una 
  abreviatura de @{term "inj_on f "} definida en la teoría
  \href{http://bit.ly/2XuPQx5}{Fun.thy}. Además, contiene la definición
  de @{term "inj_on"}
  \begin{itemize}
    \item[] @{thm[mode=Rule] inj_on_def[no_vars]}
      \hfill (@{text inj_on_def})
  \end{itemize} 
  Por su parte, @{term UNIV} es el conjunto universal definido en la 
  teoría \href{http://bit.ly/2XtHCW6}{Set.thy} como una abreviatura de 
  @{term top} que, a su vez está definido en la teoría 
  \href{http://bit.ly/2Xyj9Pe}{Orderings.thy} mediante la siguiente
  propiedad 
  \begin{itemize}
    \item[] @{thm[mode=Rule] ordering_top.extremum[no_vars]} 
      \hfill (@{text ordering_top.extremum})
  \end{itemize} 
  En el caso de la teoría de conjuntos, la relación de orden es la
  inclusión de conjuntos.

  Presentaremos distintas demostraciones de los lemas.\<close>

subsection \<open>Demostración estructurada de los lemas\<close>
 
text \<open>Las demostraciones declarativas son las siguientes:\<close>

lemma condicion_necesaria_detallada:
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) \<longrightarrow> (g = h)"
proof (rule impI)
  assume "f \<circ> g = f \<circ> h"
  show "g = h"
  proof (rule ext)
    fix x
    have "(f \<circ> g)(x) = (f \<circ> h)(x)" 
      by (simp only: \<open>f \<circ> g = f \<circ> h\<close>)
    then have "f(g(x)) = f(h(x))" 
      by (simp only: comp_apply) 
    then show "g(x) = h(x)"
      using \<open>inj f\<close> 
      by (simp only: injD)
  qed
qed

text \<open>\comentario{Añadir al glosario injD.}\<close>

(* declare [[show_types]] *)

lemma condicion_suficiente_detallada:
  assumes "\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
  shows "inj f"
proof (rule injI)
  fix a b 
  assume "f a = f b"
  let ?g = "\<lambda>x :: 'a. a"
  let ?h = "\<lambda>x :: 'a. b"
  have "\<forall>h. (f \<circ> ?g = f \<circ> h \<longrightarrow> ?g = h)"
    using assms 
    by (rule allE) 
  then have "(f \<circ> ?g = f \<circ> ?h \<longrightarrow> ?g = ?h)"  
    by (rule allE)
  moreover
  have "f \<circ> ?g = f \<circ> ?h" 
  proof (rule ext)
    fix x
    have "(f \<circ> (\<lambda>x :: 'a. a)) x = f(a) " 
      by (simp only: comp_apply)
    also have "... = f(b)" 
      by (simp only: \<open>f a = f b\<close>)
    also have "... =  (f \<circ> (\<lambda>x :: 'a. b)) x" 
      by (simp only: comp_apply)
    finally show " (f \<circ> (\<lambda>x. a)) x =  (f \<circ> (\<lambda>x. b)) x"
      by this
  qed
  ultimately have "?g = ?h" 
    by (rule mp)
  then show " a = b" 
    by (rule fun_cong)
qed

text \<open>
\begin{nota}
En la demostración de condición suficiente detallada, es necesario
 especificar los tipos tanto de las funciones como de los elementos. Ya
 que en caso de no especificarlo toma el tipo más general
 posible y no se puede demostrar.
\end {nota}
En las anteriores demostraciones se han introducido las reglas: 
  \begin{itemize}
    \item[] @{thm[mode=Rule] fun_cong[no_vars]} 
      \hfill (@{text fun_cong})
    \item[] @{thm[mode=Rule] comp_apply[no_vars]} 
      \hfill (@{text comp_apply})
  \end{itemize}
  Otras demostraciones declarativas no detalladas usando demostradores 
  automáticos metis, auto y blast son:\<close>

lemma condicion_necesaria_1:
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) \<longrightarrow>(g = h)"
proof 
  assume "f \<circ> g = f \<circ> h" 
  then show "g = h" 
    using `inj f` 
    by (simp add: inj_on_def fun_eq_iff) 
qed

lemma condicion_suficiente_1:
  fixes f :: "'b \<Rightarrow> 'c" 
  assumes "\<forall>(g :: 'a \<Rightarrow> 'b) (h :: 'a \<Rightarrow> 'b). (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
  shows "inj f"
proof (rule injI)
  fix a b 
  assume "f a = f b"
  let ?g = "\<lambda>x :: 'a. a"
  let ?h = "\<lambda>x :: 'a. b"
  have "(f \<circ> ?g = f \<circ> ?h \<longrightarrow> ?g = ?h)" using assms by blast
  moreover  
  have "f \<circ> ?g = f \<circ> ?h" 
  proof 
    fix x
    have " (f \<circ> (\<lambda>x :: 'a. a)) x = f(a) " by simp
    also have "... = f(b)" using \<open>f a = f b\<close> by simp
    also have "... =  (f \<circ> (\<lambda>x :: 'a. b)) x" by simp
    finally show "(f \<circ> (\<lambda>x :: 'a. a)) x =  (f \<circ> (\<lambda>x :: 'a. b)) x" by simp
  qed
  ultimately have "(\<lambda>x :: 'a. a) = (\<lambda>x :: 'a. b)" by blast
  then show "a = b" by metis 
qed

subsection \<open>Demostración del teorema en Isabelle/Hol\<close>

text \<open>En consecuencia, la demostración de nuestro teorema: \<close>

theorem caracterizacion_inyectividad:
  "inj f \<longleftrightarrow> (\<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
proof
  assume "inj f"
  show "\<forall>g h. f \<circ> g = f \<circ> h \<longrightarrow> g = h"
  proof (intro allI)
    fix g h
    show "f \<circ> g = f \<circ> h \<longrightarrow> g = h"
      using \<open>inj f\<close>
      by (rule condicion_necesaria_detallada)
  qed
next 
  assume "\<forall>g h. f \<circ> g = f \<circ> h \<longrightarrow> g = h"
  then show "inj f"
    by (simp only: condicion_suficiente_detallada)
qed

text \<open>Su demostración automática es\<close>

theorem "inj f \<longleftrightarrow> (\<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
  using condicion_necesaria_detallada condicion_suficiente_detallada 
  by auto

(*<*)
end
(*>*) 
