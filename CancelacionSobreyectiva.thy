(*<*) 
theory CancelacionSobreyectiva 
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

section \<open>Cancelación de las funciones sobreyectivas\<close>

text \<open>
El siguiente teorema prueba una caracterización de las funciones
 sobreyectivas, en otras palabras, las funciones sobreyectivas son
 epimorfismos en la categoría de conjuntos. Donde un epimorfismo es un
 homomorfismo sobreyectivo y la categoría de conjuntos es la categoría
 donde los objetos son conjuntos.


\begin {teorema}
  f es sobreyectiva si y solo si  para todas funciones g y h tal que g o f
 = h o f se tiene que g = h.
\end {teorema}
 
El teorema lo podemos dividir en dos lemas, ya que el teorema se
 demuestra por una doble implicación, luego vamos a dividir el teorema
 en las dos implicaciones.

\begin {lema}
  f es sobreyectiva entonces  para todas funciones g y h tal que g o f
 = h o f se tiene que g = h.
\end {lema}
\begin {demostracion}
\begin {itemize}
\item Supongamos que tenemos que $g \circ  f = h \circ f$, queremos probar que $g =
 h.$ Usando la definición de sobreyectividad $(\forall y \in Y,
 \exists x | y = f(x))$ y nuestra hipótesis, tenemos que:
$$g(y) = g(f(x)) = (g o f) (x) = (h o f) (x) = h(f(x)) = h(y)$$
\item Supongamos que $g = h$, hay que probar que $g o f = h o f.$ Usando
nuestra hipótesis, tenemos que:
$$ (g o f)(x) = g(f(x)) = h(f(x)) = (h o f) (x).$$
\end {itemize}
.
\end {demostracion}

\begin {lema}
 Si  para todas funciones g y h tal que g o f  = h o f se tiene
 que g = h entonces f es sobreyectiva.
\end {lema}


Su especificación es la siguiente, que la dividiremos en dos al igual que 
en la demostración a mano: 
\<close>

theorem
 "surj f \<longleftrightarrow> (g \<circ> f = h \<circ> f) = (g = h)"
  oops

lemma 
"surj f \<Longrightarrow>  (g \<circ> f = h \<circ> f) = (g = h)"
  oops

lemma 
"\<forall>g h. (g \<circ> f = h \<circ> f \<longrightarrow> g = h) \<longrightarrow> surj f"
  oops


  text \<open>
En la especificación anterior, @{term "surj f"} es una abreviatura de 
  @{text "range f = UNIV"}, donde @{term "range f"} es el rango o imagen
de la función f.
 Por otra parte, @{term UNIV} es el conjunto universal definido en la 
  teoría \href{http://bit.ly/2XtHCW6}{Set.thy} como una abreviatura de 
  @{term top} que, a su vez está definido en la teoría 
  \href{http://bit.ly/2Xyj9Pe}{Orderings.thy} mediante la siguiente
  propiedad 
  \begin{itemize}
    \item[] @{thm[mode=Rule] ordering_top.extremum[no_vars]} 
      \hfill (@{text ordering_top.extremum})
  \end{itemize} 
Además queda añadir que la teoría donde se encuentra definido @{term"surj f"}
 es en \href{http://bit.ly/2XuPQx5}{Fun.thy}. Esta teoría contiene la
 definicion @{term" surj_def"}.
 \begin{itemize}
    \item[] @{thm[mode=Rule] surj_def[no_vars]} \hfill (@{text inj_on_def})
  \end{itemize} 

Presentaremos distintas demostraciones del teorema. La primera es la
 detallada:
\<close>

lemma 
  assumes "surj f" 
  shows "( g \<circ> f = h \<circ> f ) = (g = h)"
proof (rule iffI)
  assume 1: " g \<circ> f = h \<circ> f "
  show "g = h" 
  proof 
    fix x

    have " \<exists>y . x = f(y)" using assms by (simp add:surj_def)
    then obtain "y" where 2:"x = f(y)" by (rule exE)
    then have "g(x) = g(f(y))" by simp
    also have "... = (g \<circ> f) (y)  " by simp
    also have "... = (h \<circ> f) (y)" using 1 by simp
    also have "... = h(f(y))" by simp
    also have "... = h(x)" using 2   by (simp add: \<open>x = f y\<close>)
    finally show  " g(x) = h(x) " by simp
  qed
next
  assume "g = h" 
  show "g \<circ> f = h \<circ> f"
  proof
    fix x
    have "(g \<circ> f) x = g(f(x))" by simp
    also have "\<dots> = h(f(x))" using `g = h` by simp
    also have "\<dots> = (h \<circ> f) x" by simp
    finally show "(g \<circ> f) x = (h \<circ> f) x" by simp
  qed
qed


text \<open>En la demostración hemos introducido: 
 \begin{itemize}
    \item[] @{thm[mode=Rule] exE[no_vars]} 
      \hfill (@{text "rule exE"}) 
  \end{itemize} 
 \begin{itemize}
    \item[] @{thm[mode=Proof] iffI[no_vars]} 
      \hfill (@{text iffI})
  \end{itemize} 

La demostración aplicativa es: \<close>

lemma "surj f \<Longrightarrow> ((g \<circ> f) = (h \<circ> f) ) = (g = h)"
  apply (simp add: surj_def fun_eq_iff)
  apply (rule iffI)
   prefer 2
  apply auto
 
  apply  metis

  done

lemma "surj f \<Longrightarrow> ((g \<circ> f) = (h \<circ> f) ) = (g = h)"
  apply (simp add: surj_def fun_eq_iff ) 
  by metis


text \<open>En esta demostración hemos introducido:
 \begin{itemize}
    \item[] @{thm[mode=Rule] fun_eq_iff[no_vars]} 
      \hfill (@{text fun_eq_iff})
  \end{itemize} 
\<close>
  
    



 
(*<*)
end 
(*>*)