(* Teorema de Knaster-Tarski *)

(*<*) 
theory TeoremaKnasterTarski
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
 "HOL-Library.Lattice_Syntax"
begin
(*>*) 

section\<open>Teorema de Kanster Tarski \<close>


subsection \<open>Demostración en lenguaje natural \<close>

text  \<open>\comentario{Añadir ejemplos de retículos (y también de conjuntos con relaciones
  de orden que no son retículos).}
  \<close>



text \<open>El siguiente teorema, denominado teorema de Knaster-Tarski del 
punto fijo, es un teorema de la teoría de retículos y lleva el nombre de
los matemáticos Bronislaw Knaster y Alfred Tarski.

Para la exposición y demostración del teorema es necesario definir una
 serie de  conceptos previos.

\begin{definicion}
Sea L un conjunto. Un orden parcial sobre L es una relación binaria
 $\leq$ sobre L, tal que $\forall x,y,z \in L$ se verifica:
\begin {enumerate}
\item $x \leq x$ (Propiedad reflexiva).
\item Si $x \leq y$ e $y \leq x$ entonces $x = y$ (Propiedad
 antisimétrica). 
\item Si $x \leq y$ e $y \leq z$ esto implica que $x \leq z$ (Propiedad
 transitiva).
\end{enumerate}
\end{definicion}

\begin{definicion}
Un conjunto $L$ equipado con un relación de orden $(\leq)$ se denomina
 conjunto parcialmente ordenado y se denota $(L,\leq).$
\end{definicion}

A partir de ahora se considerará L como un conjunto parcialmente
 ordenado.

\begin{definicion}
Se denotará por supremo de L(sup L), si existe, al mínimo elemento de L que es
 mayor o igual que cada elemento de L. 
\end{definicion}

\begin{definicion}
Se denotará por ínfimo de L(inf L), si existe, al máximo elemento de L que es
 menor o igual que cada elemento de L. 
\end{definicion}

\begin{definicion}
Sea L un conjunto no vacío parcialmente ordenado. Se dirá que L es un
 retículo si: 
\begin{enumerate}
\item Si $\forall a,b \in L$ existe sup$(\{a,b\}).$
\item Si $\forall a,b \in L$ existe inf$(\{a,b\}).$
\end{enumerate}
\end{definicion}

\begin{definicion}
Sea L un conjunto parcialmente ordenado no vacío. Se dirá que $L$ es un
 retículo completo si $\forall S \subset L$ existe sup$(S)$ e inf$(S).$
\end{definicion}

\begin{ejemplo}
Ahora vamos a dar una serie de ejemplos de conjuntos que son
 retículos, retículos completos y algunos que no son retículos.

\begin{itemize}
\item Los subconjuntos de un conjunto dado con la relación de orden la
 inclusión es un retículo y el supremo está dado por la unión y el
 ínfimo por la intersección.
\item Los enteros no negativos dado con la relación de orden la
 divisibilidad es un retículo con el ínfimo el mínimo común múltiplo y
 el supremo el máximo común divisor.
\item Los enteros no negativos dado con la relación de orden la
 divisibilidad es un retículo completo siendo el ínfimo de este conjunto
el 1 ya que divide a cualquier número y siendo el supremo el 0 ya
 que es divisible por cualquier número.
\item Un ejemplo de un conjunto paricalmente ordenado, pero que no es un
retículo es el conjunto $\{ \emptyset, \{0\}, \{1\} \}$ con la relación
 de orden la inclusión. No es un retículo ya que el $\{0\}$ y el $\{1\}$
no tienen supremo.
\end{itemize}
\end{ejemplo}

\begin{definicion}
Una función $f: L \longrightarrow R$ entre dos conjuntos parcialmente 
ordenados, \\ $(L,\leq)$ y $(R,\leq ')$ respectivamente. Se dirá que es 
 monótona si conserva el orden, es decir, si $x \leq y
$ implica $f(x) \leq ' f(y)$ o $x \geq y$ implica $f(x) \geq ' f(y).$
\end{definicion}

\begin{definicion}
Diremos que $x$ es un punto fijo de una función si y solo si $f(x) = x.$
\end{definicion}

El enunciado del teorema es el siguiente: 

\begin{teorema}
Sea $L$ un retículo completo y $f: L \longrightarrow L$ una función
 monótona. Entonces $\exists a \in L$ punto fijo de $f.$
\end{teorema}

\begin{demostracion}
Hay que probar que $\exists a \in L$ tal que $f(a) = a.$ \\
Sea $H = \{ x \in L | f(x) \leq x\}$ y $a = \cap H.$ Por ser $L$ un
 retículo completo y $H \subset L$ sabemos que $\exists inf(H)$ y $sup(H).$
 Tenemos que $a \leq x \, \forall x \in H.$ Como $f$ es monótona, $f(a) 
\leq f(x)$ y como $x \in H$ se tiene que $f(a) \leq f(x) \leq x.$ Por lo
 que $f(a)$ es el ínfimo de $H,$ de donde obtenemos que $f(a) \leq a.$
Ahora veamos que $f(a) \geq a$ y ya se tendría probado el teorema.
 En efecto, como $f$ es monótona se tiene que $f(f(a)) \leq f(a).$
 Esto implica que $f(a) \in H,$ luego $a \leq f(a).$
\end{demostracion}
\<close>

text  \<open>\comentario{Explicar con más detalle la demostración..}
  \<close>


theorem Knaster_Tarski:
  fixes f :: "'a :: complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "\<exists>a. f a = a"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a = ?a"
  proof -
    have "f ?a \<le> ?a"
    proof (rule Inf_greatest)
      fix x
      assume "x \<in> ?H"
      then have "?a \<le> x" 
        by (rule Inf_lower)
      with \<open>mono f\<close> have "f ?a \<le> f x"
        by (rule monoD)
      also have "f x \<le> x" 
        using \<open>x \<in> ?H\<close> 
        by (rule CollectE)
      finally show "f ?a \<le> x" 
        by this
    qed
    from \<open>mono f\<close> and \<open>f ?a \<le> ?a\<close> have "f (f ?a) \<le> f ?a" 
      by (rule monoD)
    then have "f ?a \<in> ?H" 
      by (rule CollectI)
    then have "?a \<le> f ?a" 
      by (rule Inf_lower)
    show ?thesis 
      using \<open>f ?a \<le> ?a\<close> 
            \<open>?a \<le> f ?a\<close>
      by (rule order_antisym)
  qed
qed




(*<*)
end
(*>*)
