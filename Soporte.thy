(*<*) 
theory Soporte
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*) 

text \<open>En este apéndice se recogen la lista de los lemas usados en
  el trabajo indicando la página del
  \href{http://isabelle.in.tum.de/website-Isabelle2019/dist/library/HOL/HOL/document.pdf}{libro de HOL}
 donde se encuentra.\<close>

section \<open>Las bases de lógica de orden superior (2)\<close>

subsection \<open>Lógica primitiva (2.1)\<close>
subsubsection \<open>Axiomas y definiciones básicas (2.1.4)\<close>
text \<open> 
\begin{itemize}
 \item (p. 36) @{thm[mode=Rule] mp}
    \hfill (@{text mp}) 
 \item (p. 36) @{thm[mode=Rule] impI}
    \hfill (@{text impI}) 
 \item (p. 36) @{thm[mode=Rule] ext}
    \hfill (@{text ext})
 \item (p. 36) @{thm[mode=Rule] subst}
    \hfill (@{text subst}) 
\end{itemize}
\<close>
subsection \<open> Reglas fundamentales (2.2)\<close>

subsubsection \<open>Reglas de congruencia para aplicaciones (2.2.2) \<close>
text\<open>
\begin{itemize}
 \item (p. 37) @{thm[mode=Rule] fun_cong}
    \hfill (@{text fun_cong}) 
\end{itemize}
\<close>

subsubsection \<open>Igualdades de booleanos (2.2.3) \<close>
text \<open>
\begin{itemize}
\item (p.38) @{thm[mode=Rule] rev_iffD2}
 \hfill (@{text rev_iffD2})
\end{itemize}
\<close>
subsubsection \<open>Cuantificadores universales(1) (2.2.5) \<close>
text \<open>
\begin{itemize}
 \item (p. 38) @{thm[mode=Rule] allE}
    \hfill (@{text allE}) 
\end{itemize}
\<close>

subsubsection \<open> Negación (2.2.7) \<close>
text \<open>
\begin{itemize}
\item (p. 39) @{thm[mode=Rule] notE}
    \hfill (@{text notE}) 
\end{itemize}
\<close>
subsubsection \<open>Implicación (2.2.8) \<close>

text \<open>
\begin{itemize}
 \item (p. 40) @{thm[mode=Rule] not_sym}
    \hfill (@{text not_sym}) 
\end{itemize}
\<close>
subsubsection \<open>Derivación de iffI (2.2.10) \<close>

text \<open>
\begin{itemize}
 \item (p. 40) @{thm[mode=Rule] iffI}
    \hfill (@{text iffI}) 

\end{itemize}
\<close>
subsubsection \<open>Cuantificadores universales(2) (2.2.12)\<close>
text\<open>
\begin{itemize}
 \item (p. 41) @{thm[mode=Rule] allI}
    \hfill (@{text allI}) 
\end{itemize}
\<close>

subsubsection \<open>Cuantificadores existenciales (2.2.13) \<close>

text \<open>
\begin{itemize}
 \item (p. 41) @{thm[mode=Rule] exE}
    \hfill (@{text exE}) 
\end{itemize}

\<close>

subsubsection \<open>Conjunciones (2.2.14) \<close>
text \<open>
\begin{itemize}
 \item (p. 42) @{thm[mode=Rule] ccontr}
    \hfill (@{text ccontr}) 
\end{itemize}
\<close>

section \<open>Órdenes abstractos (4)  \<close>

subsection \<open>Monotonicidad (4.9)\<close>

text \<open>
\begin{itemize}
 \item (p. 95) @{thm[mode=Rule] monoD}
    \hfill (@{text monoD}) 
\end{itemize}
\<close>

subsection \<open>Nombres duplicados (4.17) \<close>


text \<open>
\begin{itemize}
 \item (p. 107) @{thm[mode=Rule] order_antisym}
    \hfill (@{text order_antisym}) 
\end{itemize}
\<close>

section \<open> Grupos (5) \<close>

subsection \<open>Soporte para razonar sobre signos (5.7)  \<close>

text \<open>
\begin{itemize}
   
    \item(p.204) @{thm[mode=rule] le_add_same_cancel1}
      \hfill (@{text le_add_same_cancel1 })
    \item(p. 204) @{thm[mode=rule] le_add_same_cancel2}
      \hfill (@{text le_add_same_cancel2 })
\end{itemize}
\<close>


section \<open>Retículos abstractos (6)\<close>

subsection \<open>Retículos concretos (6.3) \<close>
text \<open>
\begin{itemize}
 \item (p. 140) @{thm[mode=Rule] Inf_greatest}
    \hfill (@{text Inf_greatest}) 
\end{itemize}
\<close>
section \<open>Teoría de conjuntos para lógica de orden superior(7) \<close>
subsection \<open>Conjuntos como prediados \<close>
text \<open>
\begin{itemize}
 \item (p. 157) @{thm[mode=Rule] CollectD}
    \hfill (@{text CollectD})
 \item (p. 157) @{thm[mode=Rule] CollectI}
    \hfill (@{text CollectI})
 \item (p. 157) @{thm[mode=Rule] CollectE}
    \hfill (@{text CollectE})
\end{itemize}
\<close>

subsection \<open>Operaciones básicas (7.3) \<close>

subsubsection \<open> Conjunto vacío (7.3.3\<close>
text \<open>
\begin{itemize}
  \item(p. 206) @{thm[mode=rule] ball_empty} 
      \hfill (@{text ball_empty})

\end{itemize}
\<close>

subsubsection \<open>Aumentando un conjunto (7.3.10) \<close>

text \<open>
\begin{itemize}
     \item(p. 170) @{thm[mode=rule] insert_iff}
      \hfill (@{text insert_iff })
\end{itemize}
\<close>
section \<open>Nociones sobre funciones (9) \<close>

subsection \<open>El operador composición (9.2) \<close>

text \<open>
\begin{itemize}
  \item(p. 199) @{thm[mode=Rule] comp_apply[no_vars]} 
      \hfill (@{text comp_apply})
\end{itemize}
\<close>

subsection \<open>Inyectividad y biyectividad (9.5) \<close>

text \<open>
\begin{itemize}
 \item (p. 213) @{thm[mode=Rule] injD}
    \hfill (@{text injD}) 
\end{itemize}
\<close>
subsection \<open>Actualización de funciones (9.6) \<close>
text\<open>
\begin{itemize}
 \item (p. 213) @{thm[mode=Rule] fun_upd_other}
    \hfill (@{text fun_upd_other}) 
 \item (p. 213) @{thm[mode=Rule] fun_upd_same}
    \hfill (@{text fun_upd_same}) 
\end{itemize}
\<close>

section \<open>Retículos completos (10) \<close>

subsection \<open>Retículos completos abstractos (10.3) \<close>
text \<open>
\begin{itemize}
 \item (p. 220) @{thm[mode=Rule] Inf_lower}
    \hfill (@{text Inf_lower}) 
\end{itemize}
\<close>

  
section \<open>Números naturales (16)\<close>

subsection \<open>Operaciones aritméticas (16.3)\<close>

text \<open>
\begin{itemize}
  \item (p. 348) @{thm[mode=Rule] mult_0}
    \hfill (@{text mult_0}) 
  \item (p. 348) @{thm[mode=Rule] mult_Suc}
    \hfill (@{text mult_Suc}) 
  \item (p. 348) @{thm[mode=Rule] mult_Suc_right}
    \hfill (@{text mult_Suc_right}) 
 \item (p. 348) @{thm[mode=Rule] mult_0_right}
    \hfill (@{text mult_0_right}) 
\end{itemize}


\<close>
section \<open>Conjuntos finitos(18) \<close>

subsection \<open>Predicados para conjuntos finitos \<close>
text \<open>
\begin{itemize}
 \item (p. 419) @{thm[mode=Rule] finite_induct}
    \hfill (@{text finite_induct}) 
\end{itemize}
\<close>

section \<open>Método de prueba Meson (37)\<close>
subsection \<open>Forma de negación normal (37.1) \<close>
text \<open>
\begin{itemize}
 \item (p. 740) @{thm[mode=Rule] Meson.not_exD}
    \hfill (@{text Meson.not_exD}) 
\item (p. 740) @{thm[mode=Rule] Meson.not_allD}
    \hfill (@{text Meson.not_allD}) 
\end{itemize}



\<close>
(*<*)
end
(*>*) 
