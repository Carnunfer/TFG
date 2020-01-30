(* Cancelación de las funciones sobreyectivas *)

(*<*) 
theory CancelacionSobreyectiva 
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

text \<open>\comentario{Añadir lemas usados al Soporte.}\<close>

section \<open>Cancelación de las funciones sobreyectivas \<close>

subsection \<open>Demostración en lenguaje natural \<close>

text \<open>El siguiente teorema prueba una caracterización de las funciones
  sobreyectivas. Primero se definirá el significado de la sobreyectividad 
  de una función y de la propiedad de ser cancelativa por la derecha. 

  Una función $f: A \longrightarrow B$ es sobreyectiva si 
  $$\forall y \in B : \exists x \in A : f(x) = y$$

  Una función $f : A \longrightarrow B$ tiene la propiedad de ser
  cancelativa por la derecha si: 
  $$\forall C : (\forall g,h: B \longrightarrow C) : g \circ f = h \circ f
    \Longrightarrow g = h$$

  El teorema es el siguiente: 

  \begin {teorema}
    La función f es sobreyectiva si y solo si $\#C \geq 2$ y f es
    cancelativa por la derecha.
  \end {teorema}
 
  El teorema se puede dividir en dos lemas, ya que se demuestra por una
  doble implicación. 

  \begin {lema}[Condición necesaria]
    Si $f$ es sobreyectiva, entonces f es cancelativa por la derecha.
  \end {lema}

  \begin {demostracion}
  Sean $g,h: B \longrightarrow C$ tales que $g \circ  f = h \circ f$, 
  se quiere probar que $g = h.$ Usando la definición de sobreyectividad
  $(\forall y \in Y,  \exists x | y = f(x))$ y la hipótesis,
  tenemos que: 
  $$g(y) = g(f(x)) = (g \circ f) (x) = (h \circ f) (x) = h(f(x)) = h(y).$$
  \end {demostracion}

  \begin {lema}[Condición suficiente] 
  Si f es cancelativa por la derecha y $\# C \geq 2$ entonces f es sobreyectiva.
  \end {lema}

  \begin {demostracion}
  Para la demostración del lema, primero se debe señalar los
  dominios y codominios de las funciones que se van a usar.
  $f : C \longrightarrow A,$ $g,h: A \longrightarrow B.$

  La prueba se va a realizar por reducción al absurdo. Luego supongamos
  que nuestra función $f$ no es sobreyectiva, es decir, 
  $\exists y_{1} \in A \ @{text " tal que "} \  \nexists x \in C \ : 
   f(x) = y.$ 

  Definamos ahora las funciones $g,h:$
  $$g(y) = a \  \forall y \in A$$
  $$h(y)= \left\{\begin{array}{lcc}
                   a &   si  & y \neq y_1 \\
                   b &  si & y = y_1
                 \end{array}
          \right.$$

  Entonces $g(y) \neq h(y).$ Sin embargo, por hipótesis se tiene que si 
  $g \circ f = h \circ f$, lo cual es cierto, entonces $h = g$. Por lo 
  que hemos llegado a una contradicción, por lo tanto, $f$ es
  sobreyectiva. 
  \end {demostracion} 
\begin{nota}
En la condición necesaria, no es necesario que $\# C \geq 2$ a la hora
 de su demostración pero en la suficiente sí, luego el teorema lo debe
 de incluir.
\end{nota}
\<close>
subsection \<open>Especificación en Isabelle/Hol \<close>

text \<open>Su especificación es la siguiente, que se dividirá en dos al igual 
  que en la demostración a mano: \<close>

definition cancelativaDerecha :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
  "cancelativaDerecha  f =
   (\<forall>(g :: 'b \<Rightarrow> bool)  h. (g \<circ> f = h \<circ> f \<longrightarrow> g = h))"

theorem caracterizacion_funciones_sobreyectivas:
  "surj f \<longleftrightarrow> cancelativaDerecha f"
  oops

lemma condicion_suficiente:
  "surj f \<Longrightarrow> cancelativaDerecha f"
  oops

lemma condicion_necesaria:
  "cancelativaDerecha f \<Longrightarrow> surj f"
  oops

text \<open>En la especificación anterior, @{term "surj f"} es una abreviatura de
  @{text "range f = UNIV"}, donde @{term "range f"} es el rango o imagen
  de la función f y @{term UNIV} es el conjunto universal definido en la 
  teoría \href{http://bit.ly/2XtHCW6}{Set.thy} como una abreviatura de 
  @{term top} que, a su vez está definido en la teoría 
  \href{http://bit.ly/2Xyj9Pe}{Orderings.thy} mediante la siguiente
  propiedad 
  \begin{itemize}
    \item[] @{thm[mode=Rule] ordering_top.extremum[no_vars]} 
      \hfill (@{text ordering_top.extremum})
  \end{itemize} 
  Además queda añadir que la teoría donde se encuentra definido
  @{term"surj f"} es en \href{http://bit.ly/2XuPQx5}{Fun.thy}. Esta
  teoría contiene la definicion @{term" surj_def"}.
  \begin{itemize}
    \item[] @{thm[mode=Rule] surj_def[no_vars]}
      \hfill (@{text surj__def})
  \end{itemize} 
\<close>

subsection \<open>Demostración estructurada \<close>

text \<open>Presentaremos distintas demostraciones de los lemas. Las primeras
 son las detalladas:\<close>

lemma condicion_suficiente_detallada:
  assumes "surj f" 
  shows "cancelativaDerecha f"
proof -
  have "\<forall>(g :: 'a \<Rightarrow> bool) h. (g \<circ> f = h \<circ> f \<longrightarrow> g = h)"
  proof (intro allI impI)
    fix g h :: "'a \<Rightarrow> bool"  
    assume "g \<circ> f = h \<circ> f"
    show "g = h"
    proof  (rule ext)
      fix x
      have "\<exists>y. x = f y" 
        using assms 
        by (simp only: surjD)
      then obtain "y" where "x = f y" 
        by (rule exE)
      then have "g x = g (f y)"  
        by (simp only: \<open>x = f y\<close>)
      also have "\<dots> = (g \<circ> f) y" 
        by (simp only: comp_apply)
      also have "\<dots> = (h \<circ> f) y" 
        by (simp only: \<open>g \<circ> f = h \<circ> f\<close>)
      also have "\<dots> = h (f y)" 
        by (simp only: comp_apply)
      also have "\<dots> = h x" 
        by (simp only: \<open>x = f y\<close>)
      finally show "g x = h x" 
        by this
    qed
  qed
  then show "cancelativaDerecha f"
    by (simp only: cancelativaDerecha_def)
qed

lemma condicion_necesaria_detallada_l1: 
  assumes "\<nexists>x. y = f x"
  shows "g \<circ> f = g(y := z) \<circ> f"
proof (rule ext)
  fix a
  show "(g \<circ> f) a = (g(y := z) \<circ> f) a"
  proof -
    have "\<forall>x. y \<noteq> f x"
      using assms
      by (rule Meson.not_exD)
    then have "y \<noteq> f a"  
      by (rule allE)
    then have "f a \<noteq> y"  
      by (rule not_sym)
    have "(g \<circ> f) a = g (f a)"
      by (simp only: o_apply)
    also have "\<dots> = (g(y := z)) (f a)"
      using \<open>f a \<noteq> y\<close> 
      by (rule fun_upd_other [THEN sym])
    also have "\<dots> = (g(y := z) \<circ> f) a"
      by (simp only: o_apply)
    finally show ?thesis
      by this
  qed
qed

lemma condicion_necesaria_detallada_l2:
  assumes "(\<lambda>x. a) = (\<lambda>x. a)(y := b)"
  shows "a = b"
proof -
  have "a = ((\<lambda>x. a)(y := b)) y"
    using assms
    by (rule fun_cong)
  also have "\<dots> = b"
    by (rule fun_upd_same)
  finally show "a = b"
    by this
qed

lemma condicion_necesaria_detallada:
  assumes "cancelativaDerecha f"
  shows "surj f"
proof -
  have "\<forall>y. \<exists>x. y = f x"
  proof (rule ccontr)
    assume "\<not> (\<forall>y. \<exists>x. y = f x)"
    then have "\<exists>y. \<nexists>x. y = f x" 
      by (rule Meson.not_allD)
    then obtain y0 where "\<nexists>x. y0 = f x" 
      by (rule exE)
    then have "\<forall>x. y0 \<noteq> f x" 
      by (rule Meson.not_exD)
    let ?g = "(\<lambda>x. True) :: 'b \<Rightarrow> bool"
    let ?h = "?g(y0 := False)"
    have "\<forall>(g :: 'b \<Rightarrow> bool) h . g \<circ> f = h \<circ> f \<longrightarrow> g = h"
      using assms by (simp only: cancelativaDerecha_def)
    then have "\<forall>h .(?g \<circ> f = h \<circ> f) \<longrightarrow> (?g = h)"
      by (rule allE)
    then have "(?g \<circ> f = ?h \<circ> f) \<longrightarrow> (?g = ?h)" 
      by (rule allE)
    moreover
    have "(?g \<circ> f = ?h \<circ> f)"
      using \<open>\<nexists>x. y0 = f x\<close> 
      by (rule condicion_necesaria_detallada_l1)
    ultimately have "(?g = ?h)" 
      by (rule mp)
    then have "True = False" 
      by (rule condicion_necesaria_detallada_l2)
    with True_not_False show False
      by (rule notE)
  qed
  then show "surj f" 
    using surj_def 
    by (rule rev_iffD2)
qed

text \<open>En la demostración hemos introducido: 
 \begin{itemize}
    \item[] @{thm[mode=Rule] exE[no_vars]} 
      \hfill (@{text "rule exE"}) 
    \item[] @{thm[mode=Proof] iffI[no_vars]} 
      \hfill (@{text iffI})
  \end{itemize} 
\<close>

subsection \<open>Demostración teorema \<close>

text \<open>En consecuencia, la demostración del teorema es \<close>

theorem caracterizacion_funciones_sobreyectivas:
  "surj f \<longleftrightarrow> cancelativaDerecha f"
proof (rule iffI)
  show "surj f \<Longrightarrow> cancelativaDerecha f"
    by (rule condicion_suficiente_detallada)
next
  show "cancelativaDerecha f \<Longrightarrow> surj f"
    by (rule condicion_necesaria_detallada)
qed

(* Demostración automática *)
theorem "surj f \<longleftrightarrow> cancelativaDerecha f"
  by (auto simp add: condicion_suficiente_detallada
                     condicion_necesaria_detallada)

(*<*)
end 
(*>*)