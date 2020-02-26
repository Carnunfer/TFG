(* Teorema de Knaster-Tarski *)

(*<*) 
theory TeoremaKnasterTarski
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
 "HOL-Library.Lattice_Syntax"
begin
(*>*) 

section\<open>Teorema de Knaster Tarski \<close>


subsection \<open>Demostración en lenguaje natural \<close>




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
\item Si $x \leq y$ e $y \leq z$ entonces que $x \leq z$ (Propiedad
 transitiva).
\end{enumerate}
\end{definicion}

\begin{definicion}
Un conjunto $L$ con un relación de orden $(\leq)$ se denomina
 conjunto parcialmente ordenado y se denota $(L,\leq).$
\end{definicion}


\begin{definicion}
Dado un subconjunto $S$ de un conjunto $(L,\leq)$ parcialmente ordenado,
se define el supremo de $S$(sup $S$), si existe, al mínimo elemento de
 S que mayor o igual que cada elementos de S.
\end{definicion}

\begin{definicion}
Dado un subconjunto $S$ de un conjunto $(L,\leq)$ parcialmente ordenado,
se define el ínfimo de $S$(inf $S$), si existe, al máximo elemento de
 S que menor o igual que cada elementos de S. 
\end{definicion}

\begin{definicion}
Sea $(L,\leq)$ un conjunto no vacío parcialmente ordenado. Se dirá que L es un
 retículo si: 
\begin{enumerate}
\item Si $\forall a,b \in L$ existe sup$(\{a,b\}).$
\item Si $\forall a,b \in L$ existe inf$(\{a,b\}).$
\end{enumerate}
\end{definicion}

\begin{definicion}
Sea $(L,\leq)$ un conjunto parcialmente ordenado no vacío. Se dirá que $L$ es un
 retículo completo si $\forall S \subset L$ existe sup$(S)$ e inf$(S).$
\end{definicion}

\begin{ejemplo}
Ahora vamos a dar una serie de ejemplos de conjuntos que son
 retículos, retículos completos y algunos que no son retículos.

\begin{itemize}
\item Los subconjuntos de un conjunto dado con la relación de orden la
 inclusión es un retículo y el supremo está dado por la unión y el
 ínfimo por la intersección.
\item Los enteros no negativos, con la relación de orden la
 divisibilidad es un retículo con el ínfimo el mínimo común múltiplo y
 el supremo el máximo común divisor.
\item Los enteros no negativos, con la relación de orden la
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
$ implica $f(x) \leq ' f(y)$.
\end{definicion}

\begin{definicion}
Sea  $(L,\leq)$ un conjunto parcialmente ordenado y  $f: L \longrightarrow L$.
Diremos que $x$ es un punto fijo de una función si y solo si $f(x) = x.$
\end{definicion}

El enunciado del teorema es el siguiente: 

\begin{teorema}
Sea $L$ un retículo completo y $f: L \longrightarrow L$ una función
 monótona. Entonces $\exists a \in L$ punto fijo de $f.$
\end{teorema}

\begin{demostracion}
Hay que probar que $\exists a \in L$ tal que $f(a) = a.$ \\
Sea $H = \{ x \in L | f(x) \leq x \}.$ Como L, por hipótesis, es un 
retículo completo tenemos que $\exists a = inf H,$ luego  como $a$ es una cota
 inferior se tiene que $\forall x \in H \, a \leq x.$ Como $f$ es una
 función monótona, $f(a) \leq f(x) \leq x \, \forall x \in H.$ Luego se
 obtiene que $f(a)$ es una cota inferior de $H,$ por ser cota inferior
 llegamos a que $f(a) \leq a.$ Ahora veamos que $f(a) \geq a$ y ya se
 tendría probado el teorema. En efecto, como $f$ es monótona, $f(f(a))
 \leq f(a).$ Esto implica que $f(a) \in H$ y como $a$ es cota inferior
 de $H$ entonces $a \leq f(a).$ 
\end{demostracion}
\<close>


subsection \<open> Especificación en Isabelle/HOL \<close>

text \<open>
Para la comprensión de la especificación vamos a notar una serie
de definiciones y notación que se encuentran en la teoría de retículos y retículos
completos importada en Isabelle,
\href{https://isabelle.in.tum.de/dist/library/HOL/HOL/Lattices.html}{Lattice.thy}
y \href{https://isabelle.in.tum.de/library/HOL/HOL-Lattice/CompleteLattice.html}
{LatticeComplete.thy} respectivamente. 

La notación requerida para la comprensión de la especificación y
 demostración del teorema que viene importada de 
\href{http://isabelle.in.tum.de/website-Isabelle2012/dist/library/HOL/
HOL-Library/Lattice_Syntax.html}{Lattice-Syntax.thy} es:

notation \\
  bot $(\bot)$ and \\
  top $(\top)$ and  \\
  inf  $($ infixl $\sqcap$ 70 $)$ and \\
  sup  $($ infixl $\sqcup$ 65 $)$ and \\
  Inf  $($ $\sqcap  -$ $[$900$]$ 900$)$ and \\
  Sup  $($ $\sqcup -$ $[$900$]$ 900$)$ \\



Tanto los retículos, como los retículos completos se definen en Isabelle
como clases: 

Retículo: \\
class lattice $=$ \\
  assumes ex-inf : $\exists$ inf. is-inf x y inf. \\
  assumes ex-sup : $\exists$ sup. is-sup x y sup. \\

Retículo completo: \\
class complete-lattice $=$ lattice $+$ Inf $+$ Sup $+$ bot $+$ top $+$
 \\
  assumes Inf-lower : $x \in A \Longrightarrow A \leq x$ \\
  and Inf-greatest : $(\bigwedge x. x \in A \Longrightarrow z \leq x) 
\Longrightarrow z \leq \sqcap A.$ \\
    and Sup-upper : $x \in A \Longrightarrow x \leq \sqcup A$ \\
    and Sup-least : $(\bigwedge x. x \in A \Longrightarrow x \leq z) 
\Longrightarrow \sqcup A \leq z$ \\
    and Inf-empty $[$simp$]$ : $\sqcap \{\} = \top$ \\
    and Sup-empty $[$simp$]$ : $\sqcup \{\} = \bot$ \\

Para la especificiación del teorema también debemos notar que:

$$f :: "'a :: @{text "complete_latices"} \Rightarrow 'a"$$

significa que $f$ es una función cuyo dominio y codominio es un retículo
completo.

La especifiación del teorema es: 
\<close>

theorem Knaster_Tarski:
  fixes f :: "'a :: complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "\<exists>a. f a = a"
  oops 

  text \<open> 
A continuación presentaremos distintas demostraciones del teorema.
\<close>

  subsection \<open> 
Demostración detallada
\<close>

theorem Knaster_Tarski_detallada:
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

subsection \<open> Demostración automática \<close>

theorem Knaster_Tarski_automatica:
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
        by (simp add: Inf_lower)
      then show "f ?a \<le> x" 
        by (metis (mono_tags, lifting) \<open>x \<in> ?H\<close> assms le_INF_iff 
            mem_Collect_eq mono_Inf order.trans)
    qed
    then show "f ?a = ?a" 
      by (meson CollectI Inf_lower antisym assms mono_def) 
  qed
qed


(*<*)
end
(*>*)
