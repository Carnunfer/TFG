(*<*) 
theory SumaImpares
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 


section \<open>Suma de los primeros números impares\<close>

text \<open>El primer teorema es una propiedad de los números naturales.

  \begin{teorema}
    La suma de los $n$ primeros números impares es $n^2$.
  \end{teorema}

  \begin{demostracion}
    La demostración la haremos en inducción sobre $n$.
    
    (Base de la inducción) El caso $n = 0$ es trivial.
    
    (Paso de la inducción) Supongamos que la propiedad se verifica para
    $n$ y veamos que también se verifica para $n+1$. 
 
    Tenemos que demostrar que $\sum_{j=1}^{n+1} k_j = (n+1)^2$ donde
    $k_j$ el j--ésimo impar; es decir, $k_j = 2j - 1$.

    $$\begin{array}{l}
      \sum_{j = 1}^{n+1} k_j \\
      = k_{n+1} + \sum^{n}_{j=1} k_j \\ 
      = k_{n+1} + n^2 \\
      = 2(n+1) - 1 + n^2 \\
      = n^2 + 2n + 1 \\ 
      = (n+1)^2
      \end{array}$$ 
  \end{demostracion}

  Para especificar el teorema en Isabelle, se comienza definiendo 
  la función @{term "suma_impares"} tal que @{term "suma_impares n"} es
  la suma de los $n$ primeros números impares\<close>

fun suma_impares :: "nat \<Rightarrow> nat" where
  "suma_impares 0 = 0" 
| "suma_impares (Suc n) = (2*(Suc n) - 1) + suma_impares n"

text \<open>El enunciado del teorema es el siguiente:\<close>

lemma "suma_impares n = n * n"
oops  

text \<open>En la demostración se usará la táctica @{text induct} que hace
  uso del esquema de inducción sobre los naturales:
  \begin{itemize}
  \item[] @{thm[mode=Rule] nat.induct[no_vars]} 
          \hfill (@{text nat.induct})
  \end{itemize}

  Vamos a presentar distintas demostraciones del teorema. La 
  primera es la demostración aplicativa detallada.\<close>

lemma "suma_impares n = n * n"
  apply (induct n) 
   apply (simp only: suma_impares.simps(1))
  apply (simp only: suma_impares.simps(2))
  apply (simp only: mult_Suc mult_Suc_right)
  done

text \<open>Pendiente: Comentar la demostración anterior.\<close>

text \<open>Se puede eliminar los detalles de la demostración anterior.\<close>

lemma "suma_impares n = n * n"
  apply (induct n) 
   apply simp_all
  done

text \<open>La correspondiente demostración automática es\<close>

lemma "suma_impares n = n * n"
  by (induct n) simp_all

text \<open>La demostración estructurada y detallada del lema anterior es\<close>

lemma "suma_impares n = n * n"
proof (induct n)
  have "suma_impares 0 = 0" 
    by (simp only: suma_impares.simps(1))
  also have "\<dots> = 0 * 0"
    by (simp only: mult_0)
  finally show "suma_impares 0 = 0 * 0"
    by simp
next
  fix n 
  assume HI: "suma_impares n = n * n"
  have "suma_impares (Suc n) = (2 * (Suc n) - 1) + suma_impares n" 
    by (simp only: suma_impares.simps(2))
  also have "\<dots> = (2 * (Suc n) - 1) + n * n" 
    by (simp only: HI)
  also have "\<dots> = n * n + 2 * n + 1" 
    by (simp only: mult_Suc_right)
  also have "\<dots> = (Suc n) * (Suc n)"
    by (simp only: mult_Suc mult_Suc_right)
  finally show "suma_impares (Suc n) = (Suc n) * (Suc n)" 
    by simp
qed

text \<open>En la demostración anterior se pueden ocultar detalles.\<close>

lemma "suma_impares n = n * n"
proof (induct n)
  show "suma_impares 0 = 0 * 0" by simp
next
  fix n 
  assume HI: "suma_impares n = n * n"
  have "suma_impares (Suc n) = (2 * (Suc n) - 1) + suma_impares n" 
    by simp
  also have "\<dots> = (2 * (Suc n) - 1) + n * n" 
    using HI by simp
  also have "\<dots> = (Suc n) * (Suc n)" 
    by simp
  finally show "suma_impares (Suc n) = (Suc n) * (Suc n)" 
    by simp
qed

text \<open>La demostración anterior se puede simplificar usando patrones.\<close>

lemma "suma_impares n = n * n" (is "?P n = ?Q n")
proof (induct n)
  show "?P 0 = ?Q 0" by simp
next
  fix n 
  assume HI: "?P n = ?Q n"
  have "?P (Suc n) = (2 * (Suc n) - 1) + suma_impares n" 
    by simp
  also have "\<dots> = (2 * (Suc n) - 1) + n * n" using HI by simp
  also have "\<dots> = ?Q (Suc n)" by simp
  finally show "?P (Suc n) = ?Q (Suc n)" by simp
qed

text \<open>La demostración usando otro patrón es\<close>

lemma "suma_impares n = n * n" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n 
  assume "?P n"
  then show "?P (Suc n)" by simp
qed

(*<*) 
end
(*>*) 
