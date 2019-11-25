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
  f es sobreyectiva si y solo si  para todas funciones g y h tal que 
$g \circ f  = h \circ f$ se tiene que g = h.
\end {teorema}
 
El teorema lo podemos dividir en dos lemas, ya que el teorema se
 demuestra por una doble implicación, luego vamos a dividir el teorema
 en las dos implicaciones.

\begin {lema}
  f es sobreyectiva entonces  para todas funciones g y h tal que 
$g \circ f = h \circ f$ se tiene que $g = h$.
\end {lema}
\begin {demostracion}
\begin {itemize}
\item Supongamos que tenemos que $g \circ  f = h \circ f$, queremos
 probar que $g = h.$ Usando la definición de sobreyectividad
 $(\forall y \in Y,  \exists x | y = f(x))$ y nuestra hipótesis,
 tenemos que: $$g(y) = g(f(x)) = (g \circ f) (x) = (h \circ f) (x) =
 h(f(x)) = h(y).$$
\item Supongamos que $g = h$, hay que probar que
 $g \circ f = h \circ f.$ Usando nuestra hipótesis, tenemos que:
$$ (g \circ f)(x) = g(f(x)) = h(f(x)) = (h \circ f) (x).$$
\end {itemize}
(*<*).(*>*)
\end {demostracion}

\begin {lema}
 Si  para todas funciones g y h tal que $g \circ f  = h \circ f$ se 
tiene que g = h entonces f es sobreyectiva.
\end {lema}

\begin {demostracion}
Para la demostración del ejercicios, primero debemos señalar los
 dominios y codominios de las funciones que vamos a usar.
 $f : C \longrightarrow A,$ $g,h: A \longrightarrow B.$ También debemos
 notar que nuestro conjunto  $B$ tiene que tener almenos dos elementos
 diferentes, supongamos que $B = \{a,b\}.$ \\
La prueba la vamos a realizar por reducción al absurdo. Luego supongamos
que nuestra función $f$ no es sobreyectiva, es decir, $\exists y_{1} \in
 A \ @{text " tal que "} \  \nexists x \in C \ : f(x) = y.$ \\
Definamos ahora las funciones $g,h:$
$$g(y) = a \  \forall y \in A$$
$$h(y) = a  \ @{text " si "} \  y \neq y_{1} \ h(y) =  b \ 
 @{text " si "} \  y =  y_{1}$$

Entonces sabemos que $g(y) \neq h(y)  \forall y \in A.$ Sin embargo,
 por hipótesis tenemos que si $g \circ f = h \circ f$, lo cual es
 cierto, se tiene que $h = g.$ Por lo que hemos llegado a una
 contradicción, entonces $f$ es sobreyectiva.
\end {demostracion}


Su especificación es la siguiente, que la dividiremos en dos al igual que 
en la demostración a mano: 
\<close>

theorem
 "surj f \<longleftrightarrow> (\<forall>g h.(g \<circ> f = h \<circ> f) \<longrightarrow> (g = h))"
  oops

lemma 
"surj f \<Longrightarrow>  (\<forall>g h. (g \<circ> f = h \<circ> f) \<longrightarrow> (g = h))"
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
Además queda añadir que la teoría donde se encuentra definido
 @{term"surj f"} es en \href{http://bit.ly/2XuPQx5}{Fun.thy}. Esta
 teoría contiene la definicion @{term" surj_def"}.
 \begin{itemize}
    \item[] @{thm[mode=Rule] surj_def[no_vars]}
 \hfill (@{text inj_on_def})
  \end{itemize} 

Presentaremos distintas demostraciones de los lemas. Las primeras son
 las detalladas:
\<close>
(*<*)declare [[show_types]]
(*>*)

lemma sobreyectivadetallada:
  assumes "surj f" 
  shows "\<forall>g h. ( g \<circ> f = h \<circ> f ) \<longrightarrow> (g = h)"
proof (rule allI)
  fix g :: "'a \<Rightarrow>'c" 
  show "\<forall>h. (g \<circ> f = h \<circ> f) \<longrightarrow> (g = h)"
  proof (rule allI)
    fix h
    show "(g \<circ> f = h \<circ> f) \<longrightarrow> (g = h)" 
    proof (rule impI)
      assume 1: "g \<circ> f = h \<circ> f"
      show "g = h"
      proof  
        fix x
        have " \<exists>y . x = f(y)" using assms by (simp add:surj_def)
        then obtain  "y" where 2:"x = f(y)" by (rule exE)
        then have  "g(x) = g(f(y))" by simp
        also have  "... = (g \<circ> f) (y)  " by simp
        also have  "... = (h \<circ> f) (y)" using 1 by simp
        also have  "... = h(f(y))" by simp
        also have  "... = h(x)" using 2   by (simp add: \<open>x = f y\<close>)
        finally show  " g(x) = h(x) " by simp
      qed
    qed
  qed
qed


lemma sobreyectivadetallada2:
  fixes f :: "'c \<Rightarrow> 'a" 
  assumes "\<forall>(g :: 'a \<Rightarrow> 'b) (h :: 'a \<Rightarrow> 'b). ( g \<circ> f = h \<circ> f ) \<longrightarrow> (g = h)"
  shows "surj f"
proof (rule surjI)
  assume 1:" \<not> surj f"
  have " \<not>(\<forall>y. \<exists>x. y = f x)" using 1 by (simp add: surj_def)
  then have "\<exists>y. \<nexists>x. y = f x" by simp
  then obtain y1 where "\<nexists>x. y1 = f x" by (rule exE)
  then have "\<forall>x. y1 \<noteq> f x"  by simp
  let ?g = "\<lambda>x :: 'a. a :: 'b" 
  let ?h =" fun_upd ?g y1 (b :: 'b)"
  have 2:"?g \<circ> f = ?h \<circ> f \<longrightarrow> ?g = ?h" using assms by blast
  have 3:"?g \<circ> f = ?h \<circ> f" 
    by (metis (mono_tags, lifting) fun_upd_def \<open>\<nexists>x :: 'c. (y1 :: 'a) =
 (f :: 'c \<Rightarrow> 'a) x\<close> f_inv_into_f fun.map_cong0)
  have "?g = ?h" using 2 3 by (rule mp)
  have "?g \<noteq> ?h" 
  proof 
    assume 4: "?g = ?h"
    show False
    proof -
      have "?g = fun_upd ?g y1 (b :: 'b)" using 4 by simp
      also have "... =  (\<lambda>x. if x = y1 then b else ?g x)"  by (simp add:
fun_upd_def)
      finally have 5: "?g = (\<lambda>x. if x = y1 then b else ?g x)" by simp
      show False
      proof (cases)
        oops 
       
        
      
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

lemma "surj f \<Longrightarrow> ((g \<circ> f) = (h \<circ> f) ) \<longrightarrow> (g = h)"
  apply (simp add: surj_def fun_eq_iff)
  apply metis
  done

lemma "surj f \<Longrightarrow> ((g \<circ> f) = (h \<circ> f) ) \<longrightarrow>(g = h)"
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