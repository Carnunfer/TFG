(* Teorema de Cantor *)

(*<*) 
theory TeoremaCantor
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 

section \<open>Teorema de Cantor\<close>
subsection \<open>Demostración en lenguaje natural \<close>

text \<open> El siguiente teorema, denominado  teorema de Cantor por el matemático
  Georg Cantor, es un resultado importante de la teoría de conjuntos. 
 

  Para la exposición del teorema vamos a definir una serie de conceptos:

  \begin {itemize}
    \item Conjunto de potencia $A$  $(\mathcal{P}(A))$: conjunto formado
      por todos los subconjuntos de $A$.
    \item Cardinal del conjunto $A$ (denotado $\# A$): número de
      elementos del propio conjunto.
  \end {itemize}

  El enunciado original del teorema es el siguiente :

  \begin {teorema}
    El cardinal del conjunto potencia de cualquier conjunto A es
    estrictamente mayor que el cardinal de A, o lo que es lo mismo,
    $\# \mathcal{P}(A) > \# A.$
  \end {teorema}

   El enunciado del teorema lo podemos reformular como sigue:
  \begin{teorema}
    Dado un conjunto $A$, $\nexists  f : A \longrightarrow \mathcal{P}(A)$ 
    sobreyectiva.
  \end{teorema}


  \begin{demostracion}
  La prueba se va a realizar por reducción al absurdo.

  Supongamos que $\exists f : A \longrightarrow \mathcal{P}(A)$
  sobreyectiva, es decir, $\forall B \in \mathcal{P}(A) ,  \exists x \in
  A$ tal que $B = f(x)$.

  En particular, tomemos el conjunto
  $$B = \{ x \in A : x \notin f(x) \}$$
  y supongamos que $\exists a \in A : B = f(a)$, ya que $B$ es un
  subconjunto de A. Luego podemos distinguir dos casos :

  $1.$ Si $a \in B.$

  Entonces por definición del conjunto $B$ se tiene que
  $a \notin B$, luego se llega a una contradicción. 

  $2.$ Si $a \notin B.$
  Entonces por definición de B se tiene que $a \in B$, luego se ha 
  llegado a otra contradicción. 

  En los dos casos se ha llegado a una contradicción, por lo que no
  existe $a$ y $f$ no es sobreyectiva.
  \end{demostracion} 
\<close>

subsection \<open>Especificación en Isabelle/HOL\<close>

text \<open>Para la especificación del teorema en Isabelle, primero debemos 
  notar que 
  $$f :: \, 'a \Rightarrow \,'a \: set$$ 
  significa que es una función de tipos, donde $'a$ significa un tipo y 
  para poder denotar el conjunto potencia tenemos que poner $'a \ set$ 
  que significa que es de un tipo formado por conjuntos del tipo $'a$.

  El enunciado del teorema es el siguiente : 
\<close>

theorem Cantor: "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
  oops 

text \<open>A continuación presentaremos diferentes formas de demostración del
  teorema. \<close>

subsection \<open>Demostración detallada \<close>

text \<open>La primera es la demostración detallada del teorema: \<close>

theorem
  "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>B. \<exists>x. B = f x"
proof (rule notI)
  assume "\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
  then obtain f :: "'a \<Rightarrow> 'a set" where Hf: "\<forall>A. \<exists>x. A = f x" 
    by (rule exE)
  let ?B = "{x. x \<notin> f x}"
  from Hf obtain "\<exists>x. ?B = f x " 
    by (rule allE)
  then obtain a where Ha: "?B = f a" 
    by (rule exE)
  show False
  proof (cases "a \<in> ?B")
    assume "a \<in> ?B"  
    then have "a \<notin> f a"
      by (rule CollectD)
    moreover
    have "a \<in> f a"
      using \<open>a \<in> ?B\<close>
      by (simp only: Ha)
    ultimately show False  
      by (rule notE)
  next 
    assume "a \<notin> ?B"
    with Ha have "a \<notin> f a" 
      by (rule subst)
    moreover 
    have "a \<in> f a"
    proof (rule ccontr)
      assume "a \<notin> f a"
      then have "a \<in> ?B"
        by (rule CollectI)
      with \<open>a \<notin> ?B\<close> show False
        by (rule notE)
    qed 
    ultimately show False  
      by (rule notE)
  qed
qed

text \<open>\comentario{Añadir los lemas usados en la prueba anterior al
  apéndice.}\<close> 

subsection \<open>Demostración automática \<close>

text \<open> La demostración automática del teorema es: \<close>

theorem Cantor: 
  "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>B. \<exists>x. B = f x"
  by best

text \<open>\comentario{Añadir el método best al apéndice.}\<close>

(*<*) end (*>*)
 
