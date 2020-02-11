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

\begin{definicion}
  Una función $f : A \longrightarrow B$ es inyectiva si 
  $$\forall x,y \in \ A : f(x) = f(y) \Longrightarrow x = y.$$
\end{definicion}

\begin{definicion}[Cancelativa izquierda]
  Una función $f : A \longrightarrow B$ es cancelativa por la izquierda
 si $$\forall C: (\forall g,h: C \longrightarrow A) : 
    f \circ g = f \circ h \Longrightarrow g = h.$$
\end{definicion}

 Se puede reformular la definición de ser cancelativa por la izquierda
 como:

\begin{definicion}[Cancelativa izquierda']
Una función $f: A \longrightarrow B$ es cancelativa por la izquierda si
 $$\forall g,h: \{0,1\} \longrightarrow A : f \circ g = f \circ h 
\Longrightarrow g = h.$$
\end{definicion}

Vamos a demostrar la equivalencia de estas dos definiciones.

\begin{lema}
Son equivalentes:
\begin{enumerate}
\item Cancelativa izquierda 
\item Cancelativa izquierda'
\end{enumerate}
\end{lema}

\begin{demostracion}


$1 \Longrightarrow 2$
Trivial, ya que tomando en particular el conjunto $C = \{0,1\}$ se tiene
probado.

$2 \Longrightarrow 1$
La prueba se va a realizar por reducción al  absurdo, es decir, 
supongamos que $\exists C : \exists g,h: C \longrightarrow A : f \circ g
= f \circ h$ y $g \neq h.$ Como $g \neq h$ esto implica que $\exists c
 \in C$ tal que $g(c) \neq h(c).$ 
Consideremos ahora $r: \{0,1\} \longrightarrow A$ tal que 
  $$r(x)= \left\{\begin{array}{lcc}
                   c &   si  & x = 0 \\
                   c &  si & x = 1
                 \end{array}
          \right.$$
Definamos entonces $g' = g \circ r$ y $h' = h \circ r.$ Luego se tiene
 que 
$$(f \circ g')(x) = (f \circ g \circ r)(x) = ((f \circ g) \circ r))(x) 
\stackrel{H.I}{=} ((f \circ h) \circ r)(x) = (f \circ h \circ r)(x) = 
(f \circ h')(x)$$

Entonces $f \circ g' = f \circ h'$ luego usando la hipótesis $g' = h'.$

Por otra parte 
$$g'(0) = (g \circ r)(0) = g(r(0)) = g(c)$$
$$h'(0) = (h \circ r)(0) = h(r(0)) = h(c)$$

Luego $g'(0) \neq h'(0)$ por lo que hemos llegado a un absurdo.
\end{demostracion}

\begin{nota}
A partir de ahora cuando se haga referencia a la definición de
 cancelativa por la izquierda se usará la segunda definición.
\end{nota}

  El teorema es el siguiente:
  \begin{teorema}
    Una función $f$ es inyectiva si y solo si es cancelativa por la
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
 Hay que probar que $\forall g,h: \{0,1\} \longrightarrow A : f \circ g
= f \circ h$ esto implica que $g = h$. Luego sean $g,h$ tales que $f
 \circ g = f \circ h,$ veamos que $\forall x. g(x) = h(x).$ Luego se
 tiene que: 
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

    Consideremos las funciones constantes $g(x) = a,  \ \forall x$  y
    $h(x) = b, \  \forall x.$
    Veamos que $f \circ g = f \circ h.$ En efecto, $\forall x$
    $$(f \circ g)(x) = f(g(x)) = f(a)$$
    $$(f \circ h)(x) = f(h(x)) = f(b)$$
    Por hipótesis se tiene que $f(a) = f(b)$ luego $f \circ g = f \circ
 h.$ Por hipótesis se tiene que $f$ es cancelativa por la izquierda, por
lo tanto, esto implica que
$$g = h \Longrightarrow g(x) = h(x), \, \forall x \Longrightarrow a =
 b.$$
\end{demostracion}
\<close>

subsection \<open>Especificación en Isabelle/Hol\<close>

text \<open>Antes de la especificación en Isabelle, vamos a definir en Isabelle
la propiedad de que una función sea cancelativa por la izquierda.\<close>



definition cancelativaIzquierda :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
  "cancelativaIzquierda  f =
   (\<forall>(g :: bool \<Rightarrow> 'a) h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h))"

text \<open>La especificación del teorema es la siguiente: \<close>
theorem caracterizacion_funcion_inyecctiva:
  "inj f \<longleftrightarrow> cancelativaIzquierda f"
  oops

  text \<open>Al igual que en la demostración a mano, se va a demostrar a través
de dos lemas asociados a cada implicación. Son los siguientes:\<close>

lemma "\<forall>g h. cancelativaIzquierda f \<Longrightarrow> inj f"
  oops

lemma "inj f \<Longrightarrow> cancelativaIzquierda f"
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
  shows "cancelativaIzquierda f"
proof -
  have "\<forall>(g :: bool \<Rightarrow> 'a) h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
  proof (intro allI impI)
    fix g h :: "bool \<Rightarrow> 'a"
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
  then show "cancelativaIzquierda f"
    by (simp only: cancelativaIzquierda_def)
qed

text \<open>\comentario{Añadir al glosario injD.}\<close>

lemma condicion_suficiente_detallada:
  assumes "cancelativaIzquierda f"
  shows "inj f"
proof (rule injI)
  fix a b 
  assume "f a = f b"
  let ?g = "\<lambda>x :: bool. a"
  let ?h = "\<lambda>x :: bool. b"
  have "\<forall>(g :: bool \<Rightarrow> 'a) h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
    using assms 
    by (simp only: cancelativaIzquierda_def)
  then have "\<forall>h. (f \<circ> ?g = f \<circ> h \<longrightarrow> ?g = h)" 
    by (rule allE) 
  then have "(f \<circ> ?g = f \<circ> ?h \<longrightarrow> ?g = ?h)"  
    by (rule allE)
  moreover
  have "f \<circ> ?g = f \<circ> ?h" 
  proof (rule ext)
    fix x :: bool
    have "(f \<circ> (\<lambda>x :: bool. a)) x = f(a) " 
      by (simp only: comp_apply)
    also have "... = f(b)" 
      by (simp only: \<open>f a = f b\<close>)
    also have "... =  (f \<circ> (\<lambda>x :: bool. b)) x" 
      by (simp only: comp_apply)
    finally show "(f \<circ> (\<lambda>x. a)) x =  (f \<circ> (\<lambda>x. b)) x"
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
  shows "cancelativaIzquierda f"
proof -
  have "\<forall>(g :: bool \<Rightarrow> 'a) h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
  proof (intro allI impI)
  fix g h :: "bool \<Rightarrow> 'a"
  assume "f \<circ> g = f \<circ> h" 
  then show "g = h" 
    using `inj f` 
    by (simp add: inj_on_def fun_eq_iff) 
  qed
  then show "cancelativaIzquierda f"
    by (simp only: cancelativaIzquierda_def)
qed

subsection \<open>Demostración del teorema en Isabelle/Hol\<close>

text \<open>En consecuencia, la demostración de nuestro teorema: \<close>

theorem caracterizacion_inyectividad:
  "inj f \<longleftrightarrow> cancelativaIzquierda f"
proof (rule iffI)
  show "inj f \<Longrightarrow> cancelativaIzquierda f"
    by (rule condicion_necesaria_detallada)
next
  show "cancelativaIzquierda f \<Longrightarrow> inj f"
    by (simp only: condicion_suficiente_detallada)
qed

text \<open>Su demostración automática es\<close>

theorem "inj f \<longleftrightarrow> cancelativaIzquierda f"
  using condicion_necesaria_detallada 
        condicion_suficiente_detallada 
  by auto

(*<*)
end
(*>*) 
