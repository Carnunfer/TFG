(*<*) 
theory ConjuntosFinitos 
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

section \<open>Propiedad de los conjuntos finitos de números naturales\<close> 

text \<open>El siguiente teorema es una propiedad que verifican todos los conjuntos finitos de números
  naturales  estudiado en el \href{http://bit.ly/2XBW6n2}{tema 10} de la
asignatura de LMF. Su enunciado es el siguiente 

  \begin{teorema} 
    Sea S un conjunto finito de números naturales.  Entonces todos los
 elementos de S son menores o iguales que la suma de los elementos de
 S, es decir, $$\forall m , m \in S \Longrightarrow m \leq \sum S$$ 
\newline
donde $\sum S $ denota la suma de todos los elementos de S.
  \end{teorema} 

\begin{demostracion}
La demostración del teorema la haremos por inducción sobre conjuntos
 finitos naturales.\\
Primero veamos el caso base, es decir, supongamos que $S = \emptyset$:

Tenemos que: $$\forall n, n \in \emptyset \Longrightarrow n \leq \sum
 \emptyset.$$\\
Ya hemos probado el caso base, veamos ahora el paso inductivo:
\newline
Sea S un conjunto finito para el que se cumple la hipótesis, es decir,
 todos los elementos de S son menores o iguales que la suma de todos sus
elementos, sea $a$ un elemento tal que $a \notin S$, ya que si $a \in S$
entonces la demostración es trivial.\\
Hay que probar: $$\forall n , n \in S \cup \{ a \} \Longrightarrow n
 \leq \sum (S \cup \{ a \})$$
Vamos a distinguir dos casos:\\
Caso 1: $n = a$ \\
Si $n = a$ tenemos que $n = a \leq a + \sum S = \sum ( S \cup \{ a
 \})$\\
Caso 2: $n \neq a$\\
Si $n \neq a$ tenemos que $a \notin S$ y que $n \in S \cup \{ a \}$,
 luego esto implica que $n \in S$ y usando la hipótesis de inducción
$$n \in S \Longrightarrow n \leq \sum S \leq \sum S + a = \sum (S \cup
 \{ a \})$$
\end{demostracion}

En la demostración del teorema hemos usado un resultado, que vamos a
 probar en Isabelle después de la especificación del teorema,
 el resultado es $\sum S + a = \sum (S \cup \{ a
 \})$.
\<close>


text  \<open>Para la especificación del teorema en isabelle, primero debemos
 notar que  @{text "finite S "} indica que nuestro conjunto $S$ es 
finito  y definir  la función @{text "sumaConj"} tal que
 @{text "sumaConj n"} esla suma de todos los elementos de S.
 \<close>

definition sumaConj :: "nat set \<Rightarrow> nat" where
  "sumaConj S \<equiv> \<Sum>S"

text \<open>El enunciado del teorema es el siguiente : \<close>


lemma "finite S \<Longrightarrow> \<forall>x\<in>S. x \<le> sumaConj S"

  oops 

  text \<open>Vamos a demostrar primero el lema enunciado anteriormente \<close>
lemma " x \<notin> S \<and> finite S \<longrightarrow> sumaConj S + x = sumaConj(insert x S)"
  by (simp add: sumaConj_def)


text  \<open>La demostración del lema anterior se ha incluido
 @{term"sumConj_def"}, que hace referencia a la definición sumaConj que
 hemos hecho anteriormente. \\
En la demostración se usará la táctica @{text induct} que hace
  uso del esquema de inducción sobre los conjuntos finitos naturales:
  \begin{itemize}
  \item[] @{thm[mode=Def] finite.induct[no_vars]} \hfill (@{text finite.induct})
  \end{itemize} 

Vamos a ver presentar las diferentes formas de demostración.


La demostración aplicativa es: \<close>

lemma "finite S \<Longrightarrow> \<forall>x\<in>S. x \<le> sumaConj S"
  apply (induct rule: finite_induct)
   apply simp
  apply (simp add: add_increasing sumaConj_def)
  done

text \<open>En la demostración anterior se ha introducido:
 \begin{itemize}
    \item[] @{thm[mode=Rule] add_increasing[no_vars]} 
      \hfill (@{text add_increasing})
  \end{itemize} 
 La demostración automática es: \<close>

lemma "finite S \<Longrightarrow> \<forall>x\<in>S. x \<le> sumaConj S"
  by (induct rule: finite_induct)
     (auto simp add:  sumaConj_def)

  text \<open>La demostración declarativa es: \<close>

lemma sumaConj_acota: 
  "finite S \<Longrightarrow> \<forall>x\<in>S. x \<le> sumaConj S"
proof (induct rule: finite_induct)
  show "\<forall>x \<in> {}. x \<le> sumaConj {}" by simp
next
  fix x and F
  assume fF: "finite F" 
     and xF: "x \<notin> F" 
     and HI: "\<forall> x\<in>F. x \<le> sumaConj F"
  show "\<forall>y \<in> insert x F. y \<le> sumaConj (insert x F)"
  proof 
    fix y 
    assume "y \<in> insert x F"
    show "y \<le> sumaConj (insert x F)"
    proof (cases "y = x")
      assume "y = x"
      then have "y \<le> x + (sumaConj F)" by simp
      also have "\<dots> = sumaConj (insert x F)"   by (simp add: fF sumaConj_def xF) 
      finally show ?thesis .
    next
      assume "y \<noteq> x"
      then have "y \<in> F" using `y \<in> insert x F` by simp
      then have "y \<le> sumaConj F" using HI by simp
      also have "\<dots> \<le> x + (sumaConj F)" by simp
      also have "\<dots> = sumaConj (insert x F)" using fF xF
        by (simp add: sumaConj_def)
      finally show ?thesis .
    qed
  qed
qed
(*<*)
text \<open> En esta última demostración hemos usado el método de prueba por
 casos,el método blast y también el simp("simplificador") añadiendole 
"sumaConj-def".
  \begin{itemize}
  \item[] @{thm[mode=Proof] finite.induct[no_vars]} \hfill (@{text finite.induct})
  \end{itemize} 

\<close>
(*>*)
(*<*)
end
(*>*)
