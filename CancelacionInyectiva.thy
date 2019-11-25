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
    $f$ es una función inyectiva, si y solo si, para todas funciones 
 $g$ y $h$  tales que  $f \circ g = f \circ h$ se tiene que $g = h$. 
  \end{teorema}

Vamos a hacer dos lemas de nuestro teorema, ya que podemos la doble 
implicación en dos implicaciones y demostrar cada una de ellas por
 separado.

\begin {lema}
$f$ es una función inyectiva si para todas funciones $g$ y $h$ tales que
 $f \circ g = f \circ h$ se tiene que $g = h.$
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
Sean $a,b$ tales que $f(a) = f(b)$, y definamos $g(x) = a  \ \forall x$
 y $h(x) = b \  \forall x$ entonces 
$$(f \circ g) = (f \circ h) \Longrightarrow  f(g(x)) = f(h(x)) \Longrightarrow f(a) = f(b)$$
Por hipótesis tenemos entonces que $a = b,$ como queríamos demostrar.
\end {demostracion}


  Su especificación es la siguiente, pero al igual que hemos hecho en la demostración
a mano vamos a demostrarlo a través de dos lemas:
\<close>

theorem caracterizacionineyctiva:
  "inj f \<longleftrightarrow> (\<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
  oops



  text \<open>Sus lemas son los siguientes: \<close>

lemma 
"\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h) \<Longrightarrow> inj f"
  oops

lemma 
"inj f \<Longrightarrow> (\<forall>g h.(f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
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
  "inj f \<Longrightarrow> (\<forall>g h.(f \<circ> g = f \<circ> h) \<longrightarrow>  (g = h))"
  apply (simp add: inj_on_def fun_eq_iff) 
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

  La demostración applicativa1 sin auto es\<close>

lemma
  "inj f \<Longrightarrow> \<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow>  (g = h)"
  apply (unfold inj_on_def) 
  apply (unfold fun_eq_iff) 
  apply (unfold o_apply)
   apply simp+
  done

lemma 
"\<forall>g h. (f \<circ> g = f \<circ> h \<longrightarrow> g = h) \<Longrightarrow> inj f"
  oops

text \<open>En la demostración anterior se ha introducido los siguientes
  hechos
  \begin{itemize}
    \item @{thm o_apply[no_vars]} \hfill (@{text o_apply})
    \item @{thm iffI[no_vars]} \hfill (@{text iffI})
  \end{itemize} 

  La demostración automática es\<close>

lemma inyectivaut:
  assumes "inj f"
  shows "\<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow> (g = h)"
  using assms
  by (auto simp add: inj_on_def fun_eq_iff) 

lemma inyectivaut2: 
  assumes "\<forall>g h. ((f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
  shows "inj f"
  using assms
  oops

  text \<open>La demostración declarativa\<close>



lemma inyectdeclarada:
  assumes "inj f"
  shows "\<forall>g h.(f \<circ> g = f \<circ> h) \<longrightarrow> (g = h)"
proof
  fix g:: "'c \<Rightarrow> 'a"
  show "\<forall>h.(f \<circ> g = f \<circ> h) \<longrightarrow> (g = h)"
  proof (rule allI)
    fix h
    show "f \<circ> g = f \<circ> h \<longrightarrow> (g = h)"
    proof (rule impI)
      assume "f \<circ> g = f \<circ> h"
      show "g = h"
      proof 
        fix x
        have  "(f \<circ> g)(x) = (f \<circ> h)(x)" using `f \<circ> g = f \<circ> h` by simp
        then have "f(g(x)) = f(h(x))" by simp
        thus  "g(x) = h(x)" using `inj f` by (simp add:inj_on_def)
      qed
    qed
  qed
qed

declare [[show_types]]

lemma inyectdeclarada2:
  fixes f :: "'b \<Rightarrow> 'c" 
  assumes "\<forall>(g :: 'a \<Rightarrow> 'b) (h :: 'a \<Rightarrow> 'b).
         (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
shows " inj f"
proof (rule injI)
  fix a b 
  assume 3: "f a = f b "
  let ?g = "\<lambda>x :: 'a. a"
  let ?h = "\<lambda>x :: 'a. b"
  have "\<forall>(h :: 'a \<Rightarrow> 'b). (f \<circ> ?g = f \<circ> h \<longrightarrow> ?g = h)"
    using assms by (rule allE)
  hence 1: " (f \<circ> ?g = f \<circ> ?h \<longrightarrow> ?g = ?h)"  by (rule allE) 
  have 2: "f \<circ> ?g = f \<circ> ?h" 
  proof 
    fix x
    have " (f \<circ> (\<lambda>x :: 'a. a)) x = f(a) " by simp
    also have "... = f(b)" using 3 by simp
    also have "... =  (f \<circ> (\<lambda>x :: 'a. b)) x" by simp
    finally show " (f \<circ> (\<lambda>x :: 'a. a)) x =  (f \<circ> (\<lambda>x :: 'a. b)) x"
      by simp
  qed
  have "?g = ?h" using 1 2 by (rule mp)
  then show " a = b" by meson
qed



text \<open>Otra demostración declarativa es\<close>

lemma inyectdetalladacorta1:
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) \<longrightarrow>(g = h)"
proof 
  assume "f \<circ> g = f \<circ> h" 
  then show "g = h" using `inj f` by (simp add: inj_on_def fun_eq_iff) 
qed

lemma inyectdetalladacorta2:
  fixes f :: "'b \<Rightarrow> 'c" 
  assumes "\<forall>(g :: 'a \<Rightarrow> 'b) (h :: 'a \<Rightarrow> 'b).
         (f \<circ> g = f \<circ> h \<longrightarrow> g = h)"
  shows " inj f"
proof (rule injI)
  fix a b 
  assume 1: "f a = f b "
  let ?g = "\<lambda>x :: 'a. a"
  let ?h = "\<lambda>x :: 'a. b"
  have 2: " (f \<circ> ?g = f \<circ> ?h \<longrightarrow> ?g = ?h)"  using assms by blast
  have 3: "f \<circ> ?g = f \<circ> ?h" 
  proof 
    fix x
    have " (f \<circ> (\<lambda>x :: 'a. a)) x = f(a) " by simp
    also have "... = f(b)" using 1 by simp
    also have "... =  (f \<circ> (\<lambda>x :: 'a. b)) x" by simp
    finally show " (f \<circ> (\<lambda>x :: 'a. a)) x =  (f \<circ> (\<lambda>x :: 'a. b)) x"
      by simp
  qed
  show  " a = b" using 2 3 by meson
qed



text \<open>En consecuencia, la demostración de nuestro teorema: \<close>

theorem caracterizacioninyectiva:
  "inj f \<longleftrightarrow> (\<forall>g h. (f \<circ> g = f \<circ> h) \<longrightarrow> (g = h))"
  using inyectdetalladacorta1 inyectdetalladacorta2 by auto





(*<*)
end
(*>*) 
