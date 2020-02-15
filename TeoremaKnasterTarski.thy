(* Teorema de Knaster-Tarski *)

(*<*) 
theory TeoremaKnasterTarski
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
 "HOL-Library.Lattice_Syntax"
begin
(*>*) 

section\<open>Teorema de Kanster Tarski \<close>

subsection \<open>Demostración en lenguaje natural \<close>

text \<open>El siguiente teorema, denominado teorema de Knaster-Tarski del 
punto fijo, es un teorema de la teoría de retículos y lleva el nombre de
los matemáticos Bronislaw Knaster y Alfred Tarski.

Para la exposición y demostración del teorema es necesario definir una
 serie de  conceptos previos.

\begin{definicion}
Una relación binaria de orden parcial es una relación binaria que es
 reflexiva, antisimétrica y transitiva.
\end{definicion}
\begin{definicion}
Un conjunto A se dice parcialmente ordenado cuando este equipado de una
 relacion binaria de orden parcial$(\leq)$. Se denotara $(A, \leq).$
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

\begin{nota}
Se notará como $x \vee y$ en lugar de sup$\{x,y\}$ cuando este exista,
 análogamente $x \wedge y$ en lugar de inf$\{x,y\}$. También se notará
 $\wedge L$ y $\vee L$  en lugar de sup L e inf L.
\end{nota}

\begin{definicion}
Sea L un conjunto parcialmente ordenado no vacío. Si $x \vee y$ y $x
 \wedge
y$ existe $\forall \, x,y \in L$ entonces L se llamará retículo.
\end{definicion}

\begin{definicion}
Sea L un conjunto parcialmente ordenado no vacío. Si $\vee L$ y $\wedge L$
 existe entonces L se llamará un retículo completo.
\end{definicion}

\begin{definicion}
Una función $f$ es monótona si conserva el orden, es decir, si $x \leq y
$ implica $f(x) \leq f(y)$ o $x \neq y$ implica $f(x) \neq f(y).$
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
Hay que probar que $\exists a \in H$ tal que $f(a) = a.$ \\
Sea $H = \{ x \in L | f(x) \leq x\}$ y $a = \cap H.$ Tenemos que $a \leq
x \, \forall x \in H$, luego $f(a) \leq f(x) \leq x.$ Por lo que $f(a)$
 es el ínfimo de $H,$ de donde obtenemos que $f(a) \leq a.$ Ahora vamos
 a probar la otra desigualdad de forma que lleguemos a la igualdad. Como
$f$ es monótona se tiene que $f(f(a)) \leq f(a).$ Esto significa que
 $f(a) \in H,$ luego $a \leq f(a).$
\end{demostracion}
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