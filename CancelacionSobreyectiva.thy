(* Cancelación de las funciones sobreyectivas *)

(*<*) 
theory CancelacionSobreyectiva 
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

text \<open>\comentario{Añadir lemas usados al Soporte.}\<close>

section \<open>Cancelación de las funciones sobreyectivas \<close>

subsection \<open>Demostración en Lenguaje natural \<close>

text \<open>El siguiente teorema prueba una caracterización de las funciones
  sobreyectivas. Primero se definirá el significado de la sobreyectividad 
  de una función y de la propiedad de ser cancelativa por la derecha. 

  Una función $f: A \longrightarrow B$ es sobreyectiva si 
  $$\forall y \in B : \exists x \in A : f(x) = y$$

  Una función $f : A \longrightarrow B$ tiene la propiedad de ser
  cancelativa por la izquierda si: 
  $$\forall C : (\forall g,h: B \longrightarrow C) : g \circ f = h \circ f
    \Longrightarrow g = h$$

  El teorema es el siguiente: 

  \begin {teorema}
    La función f es sobreyectiva si y solo si para todas funciones g y h 
    tales que $g \circ f = h \circ f$ se tiene que $g = h$.
  \end {teorema}
 
  El teorema se puede dividir en dos lemas, ya que se demuestra por una
  doble implicación. 

  \begin {lema}[Condición necesaria]
    Si $f$ es sobreyectiva, entonces para todas funciones g y h tal que 
    $g \circ f = h \circ f$ se tiene que $g = h$.
  \end {lema}

  \begin {demostracion}
  Supongamos que tenemos que $g \circ  f = h \circ f$, queremos
  probar que $g = h.$ Usando la definición de sobreyectividad
  $(\forall y \in Y,  \exists x \| y = f(x))$ y nuestra hipótesis,
  tenemos que: 
  $$g(y) = g(f(x)) = (g \circ f) (x) = (h \circ f) (x) = h(f(x)) = h(y).$$
  \end {demostracion}

  \begin {lema}[Condición necesaria] 
  Si  para todas funciones g y h tales que $g \circ f  = h \circ f$ se 
  tiene que g = h, entonces f es sobreyectiva.
  \end {lema}

  \begin {demostracion}
  Para la demostración del lema, primero se debe señalar los
  dominios y codominios de las funciones que se van a usar.
  $f : C \longrightarrow A,$ $g,h: A \longrightarrow B.$ También se debe
  notar que el conjunto $B$ tiene que tener almenos dos elementos
  diferentes,luego supongamos que $B = \{a,b\}.$ 

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
\<close>
subsection \<open>Especificación en Isabelle/Hol \<close>

text \<open>Su especificación es la siguiente, que se dividirá en dos al igual 
  que en la demostración a mano: \<close>

theorem caracterizacion_funciones_sobreyectivas:
 "surj f \<longleftrightarrow> (\<forall>g h.(g \<circ> f = h \<circ> f) \<longrightarrow> (g = h))"
  oops

lemma condicion_suficiente:
"surj f \<Longrightarrow>  (\<forall>g h. (g \<circ> f = h \<circ> f) \<longrightarrow> (g = h))"
  oops

lemma condicion_necesaria:
"\<forall>g h. (g \<circ> f = h \<circ> f \<longrightarrow> g = h) \<longrightarrow> surj f"
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
  shows "\<forall>g h. g \<circ> f = h \<circ> f \<longrightarrow> g = h"
proof (intro allI impI)
  fix g h :: "'a \<Rightarrow>'c"  
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

lemma condicion_necesaria_detallada_l1: 
  assumes "\<nexists>x. f x = y"
  shows "g \<circ> f = g(y := z) \<circ> f"
proof (rule ext)
  fix a
  show "(g \<circ> f) a = (g(y := z) \<circ> f) a"
  proof -
    have "\<forall>x. f x \<noteq> y"
      using assms
      by (rule Meson.not_exD)
    then have "f a \<noteq> y"  
      by (rule allE)
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

thm fun_upd_same

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
  fixes f :: "'a \<Rightarrow>'b"
  assumes "\<forall>(g :: 'b \<Rightarrow> 'c) h .(g \<circ> (f :: 'a \<Rightarrow> 'b) = h \<circ> f) \<longrightarrow> (g = h)"
    "\<exists>(x0 :: 'c) x1. x0 \<noteq> x1"
  shows "\<forall>y. \<exists>x. f x = y"
proof (rule ccontr)
  assume "\<not> (\<forall>y. \<exists>x. f x = y)"
  then have "\<exists>y. \<nexists>x. f x = y" 
    by (rule Meson.not_allD)
  then obtain y0 where "\<nexists>x. f x = y0" 
    by (rule exE)
  then have "\<forall>x. f x \<noteq> y0" 
    by (rule Meson.not_exD)
  obtain a0 where "\<exists>(x1::'c). a0 \<noteq> x1" 
    using assms(2) by (rule exE)
  then obtain a1 where "a0 \<noteq> a1" 
    by (rule exE)
  let ?g = "(\<lambda>x. a0) :: 'b \<Rightarrow> 'c"
  let ?h = "?g(y0 := a1)"
  have "\<forall>h .(?g \<circ> (f :: 'a \<Rightarrow> 'b) = h \<circ> f) \<longrightarrow> (?g = h)"
    using assms(1) by (rule allE)
  then have "(?g \<circ> (f :: 'a \<Rightarrow> 'b) = ?h \<circ> f) \<longrightarrow> (?g = ?h)" 
    by (rule allE)
  moreover
  have "(?g \<circ> (f :: 'a \<Rightarrow> 'b) = ?h \<circ> f)"
    using \<open>\<nexists>x :: 'a. (f :: 'a \<Rightarrow> 'b) x = (y0 :: 'b)\<close> 
    by (rule condicion_necesaria_detallada_l1)
  ultimately have "(?g = ?h)" 
    by (rule mp)
  then have "a0 = a1" 
    by (rule condicion_necesaria_detallada_l2)
  with \<open>a0 \<noteq> a1\<close> show False 
    by (rule notE)
qed

lemma condicion_necesaria_detallada_2:
  assumes " \<forall> (y::'b). (\<exists> (x:: 'a). f x = y)"
  shows "surj f"
  by (metis assms surj_def)
    
text \<open>En la demostración hemos introducido: 
 \begin{itemize}
    \item[] @{thm[mode=Rule] exE[no_vars]} 
      \hfill (@{text "rule exE"}) 
  \end{itemize} 
 \begin{itemize}
    \item[] @{thm[mode=Proof] iffI[no_vars]} 
      \hfill (@{text iffI})
  \end{itemize} 
\<close>

subsection \<open>Demostración teorema \<close>
text \<open>En consecuencia, la demostración del teorema es \<close>


theorem caracterizacion_funciones_sobreyectivas:
  fixes  g :: "'b \<Rightarrow> 'c" and 
         h :: "'b \<Rightarrow> 'c" and
         f :: "'a \<Rightarrow> 'b"
       shows "\<lbrakk> \<exists> (x0::'c) (x1::'c). x0 \<noteq> x1 \<rbrakk> \<Longrightarrow>
        surj f \<longleftrightarrow>  (\<forall>g h.(g \<circ> f = h \<circ> f) \<longrightarrow> (g = h))"
  apply (rule iffI)
   apply (rule condicion_suficiente_detallada)
   apply simp
  apply (drule condicion_necesaria_detallada)
  prefer 2
   apply (rule condicion_necesaria_detallada_2)
  oops
(*<*)
end 
(*>*)