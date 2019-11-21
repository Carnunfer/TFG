(*<*) 
theory CancelacionInyectiva
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 


section \<open>Cancelación de funciones inyectivas\<close>

text \<open>El siguiente teorema prueba una caracterización de las funciones
 inyectivas, en otras palabras, las funciones inyectivas son
 monomorfismos en la categoría de conjuntos. Un monomorfismo es un
 homomorfismo inyectivo y la categoría de conjuntos es la categoría
 cuyos objetos son los conjuntos.
  
  \begin{teorema}
    $f$ es una función inyectiva, si y solo si, para todas $g$ y $h$
    tales que @{text "f \<circ> g = f \<circ> h"} se tiene que $g = h$. 
  \end{teorema}

Vamos a hacer dos lemas de nuestro teorema, ya que podemos la doble 
implicación en dos implicaciones y demostrar cada una de ellas por
 separado.

\begin {lema}
$f$ es una función inyectiva si para todas $g$ y $h$ tales que $f \circ
 g = f \circ h$ se tiene que $g = h.$
\end {lema}
  \begin{demostracion}
    La demostración la haremos por doble implicación: 
\begin {enumerate}
\item Supongamos que tenemos que $f \circ g = f \circ h$, queremos
 demostrar que $g = h$, usando que f es inyectiva tenemos que: \\
$$(f \circ g)(x) = (f \circ h)(x) \Longrightarrow f(g(x)) = f(h(x)) = 
g(x) = h(x)$$
\item Supongamos ahora que $g = h$, queremos demostrar que  $f \circ g
 = f \circ h$. \\
$$(f \circ g)(x) = f(g(x)) = f(h(x)) = (f \circ h)(x)$$
\end {enumerate}
.
  \end{demostracion}

\begin {lema} 
Si para toda $g$ y $h$ tales que $f \circ g =  f \circ h$ se tiene que $g
= h$ entonces f es inyectiva.
\end {lema} 

\begin {demostracion}
Supongamos que el dominio de nuestra función $f$ es distinto del vacío.
Tenemos que demostrar que $\forall a,b$ tales que $f(a) = f(b),$ esto
 implica que $a = b.$ \\
Sean $a,b$ tales que $f(a) = f(b)$, sean ahora $g(x) = a \forall x$ y
 $h(x) = b \forall x$ entonces 
$$(f \circ g) = (f \circ h) \Longrightarrow  f(g(x)) = f(h(x)) \Longrightarrow f(a) = f(b)$$
Por hipótesis tenemos entonces que $a = b,$ como queríamos demostrar.
\end {demostracion}


  Su especificación es la siguiente, pero al igual que hemos hecho en la demostración
a mano vamos a demostrarlo a través de dos lemas:
\<close>

theorem 
  "inj f \<longleftrightarrow> (f \<circ> g = f \<circ> h) = (g = h)"
  oops


  text \<open>Sus lemas son los siguientes: \<close>

lemma 
"\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h) \<Longrightarrow> inj f"
  oops

lemma 
"inj f \<Longrightarrow> (f \<circ> g = f \<circ> h) = (g = h)"
  oops


text \<open>En la especificación anterior, @{term "inj f"} es una 
  abreviatura de @{term "inj_on f UNIV"} definida en la teoría
  \href{http://bit.ly/2XuPQx5}{Fun.thy}. Además, contiene la definición
  de @{term "inj_on"}
  \begin{itemize}
    \item[] @{thm[mode=Rule] inj_on_def[no_vars]} \hfill (@{text inj_on_def})
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

  Presentaremos distintas demostraciones de los lemas. La primera
  demostración es applicativa:\<close> 

lemma inyectivapli:
  "inj f \<Longrightarrow> (f \<circ> g = f \<circ> h) = (g = h)"
  apply (simp add: inj_on_def fun_eq_iff) 
  apply auto
  done 

lemma inyectivapli2:
"\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h) \<Longrightarrow> inj f"
  apply (rule injI)
  by (metis fun_upd_apply fun_upd_comp)


text \<open>En las demostraciones anteriores se han usado los siguientes
 lemas:
  \begin{itemize}
    \item[] @{thm[mode=Rule] fun_eq_iff[no_vars]} 
      \hfill (@{text fun_eq_iff})
  \end{itemize} 
  \begin{itemize}
    \item[] @{thm[mode=Rule] fun_upd_apply[no_vars]} 
      \hfill (@{text fun_upd_apply})
  \end{itemize} 
  \begin{itemize}
    \item[] @{thm[mode=Rule] fun_eq_iff[no_vars]} 
      \hfill (@{text fun_upd_comp})
  \end{itemize} 

  La demostración applicativa sin auto es\<close>

lemma
  "inj f \<Longrightarrow> (f \<circ> g = f \<circ> h) = (g = h)"
  apply (unfold inj_on_def) 
  apply (unfold fun_eq_iff) 
  apply (unfold o_apply)
  apply (rule iffI)
   apply simp+
  done

text \<open>En la demostración anterior se ha introducido los siguientes
  hechos
  \begin{itemize}
    \item @{thm o_apply[no_vars]} \hfill (@{text o_apply})
    \item @{thm iffI[no_vars]} \hfill (@{text iffI})
  \end{itemize} 

  La demostración automática es\<close>

lemma
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) = (g = h)"
  using assms
  by (auto simp add: inj_on_def fun_eq_iff) 

text \<open>La demostración declarativa\<close>

lemma
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) = (g = h)"
proof 
  assume "f \<circ> g = f \<circ> h"
  show "g = h"
  proof
    fix x
    have "(f \<circ> g)(x) = (f \<circ> h)(x)" using `f \<circ> g = f \<circ> h` by simp
    then have "f(g(x)) = f(h(x))" by simp
    then show "g(x) = h(x)" using `inj f` by (simp add:inj_on_def)
  qed
next
  assume "g = h"
  show "f \<circ> g = f \<circ> h"
  proof
    fix x
    have "(f \<circ> g) x = f(g(x))" by simp
    also have "\<dots> = f(h(x))" using `g = h` by simp
    also have "\<dots> = (f \<circ> h) x" by simp
    finally show "(f \<circ> g) x = (f \<circ> h) x" by simp
  qed
qed

text \<open>Otra demostración declarativa es\<close>

lemma 
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) = (g = h)"
proof 
  assume "f \<circ> g = f \<circ> h" 
  then show "g = h" using `inj f` by (simp add: inj_on_def fun_eq_iff) 
next
  assume "g = h" 
  then show "f \<circ> g = f \<circ> h" by simp
qed

text \<open>En consecuencia, la demostración de nuestro teorema: \<close>

theorem 
"\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h) \<longleftrightarrow> inj f"
  oops

(*<*)
end
(*>*) 
