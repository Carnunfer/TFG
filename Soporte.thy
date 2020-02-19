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
  \href{http://bit.ly/2OMbjMM}{libro de HOL} donde se encuentra.\<close>

text \<open>\comentario{Añadir el libro de HOL a la bibliografía.}\<close>

text \<open>\comentario{Completar la lista de lemas usados.}\<close>
  
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

section \<open>Las bases de lógica de orden superior (2)\<close>

subsection \<open>Lógica primitiva \<close>
subsubsection \<open>Axiomas y definiciones básicas \<close>
text \<open> 
\begin{itemize}
 \item (p. 36) @{thm[mode=Rule] mp}
    \hfill (@{text mp}) 
 \item (p. 36) @{thm[mode=Rule] impI}
    \hfill (@{text impI}) 
 \item (p. 36) @{thm[mode=Rule] ext}
    \hfill (@{text ext}) 
\end{itemize}
\<close>
subsection \<open> Reglas fundamentales (2.2)\<close>

subsubsection \<open>Reglas de congruencia para aplicaciones \<close>
text\<open>
\begin{itemize}
 \item (p. 37) @{thm[mode=Rule] fun_cong}
    \hfill (@{text fun_cong}) 
\end{itemize}
\<close>

subsubsection \<open>Cuantificadores universales(1) (2.2.5) \<close>
text \<open>
\begin{itemize}
 \item (p. 38) @{thm[mode=Rule] allE}
    \hfill (@{text allE}) 
\end{itemize}
\<close>
subsubsection \<open>Cuantificadores universales(2) (2.2.12)\<close>
text\<open>
\begin{itemize}
 \item (p. 41) @{thm[mode=Rule] allI}
    \hfill (@{text allI}) 
\end{itemize}
\<close>
(*<*)
end
(*>*) 
