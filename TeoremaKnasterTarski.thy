(* Teorema de Knaster-Tarski *)

(*<*) 
theory TeoremaKnasterTarski
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

section\<open>Teorema de Kanster Tarski \<close>

subsection \<open>Demostración en lenguaje natural \<close>

text \<open>El siguiente teorema, denominado teorema de Knaster-Tarski del 
punto fijo, es un teorema de la teoría de retículos y lleva el nombre de
los matemáticos Bronislaw Knaster y Alfred Tarski.

Para la exposición del teorema es necesario definir una serie de
 conceptos previos.

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


\<close>





(*<*)
end
(*>*)