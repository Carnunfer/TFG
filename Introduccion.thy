
(*<*) 
theory Introduccion
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 


text \<open>



La formalización matemática consiste en la implementación 
 de definiciones y pruebas de teoremas en un lenguaje de ordenador de
 forma que usando razonamientos irrefutables puedan ser verificados por
 una máquina. Su estudio se inició con la denominada demostración
 automática de teoremas, los primeros en trabajarlo y estudiarlo entre
 otros fueron Ackermann, Gödel, Church, Türing y Hilbert. 


Actualmente el gran interés de la formalización matemática es la
 capacidad de la verificación de demostraciones mediante un ordenador.
Para ello, es necesario poder expresar las definiciones, teoremas y pruebas
en un lenguaje generado por una gramática que permita verificar de forma 
mecánica las pruebas. También hay que  dotar al ordenador de una información previa al
 teorema y junto con una orientación humana se pueda llegar a validar la
demostración de los teoremas. La importancia que se le atribuye a la
 formalización es la capacidad de cálculos y razonamientos que puede
 realizar un ordenador a la vez, incluso demostrando teoremas muy
 difíciles como el teorema de los Knaster-Tarski como se verá en el
 Capítulo 5. En \cite{100theorems} podemos encontrar una lista de 100
 teoremas formalizados junto con el programa usado.  

Dentro de los sistemas de pruebas automáticas los más usados como se 
puede ver en \cite{Provers}  son HOL, Mizar, PVS, Coq, Isabelle/Isar
 entre otros. Isabelle proporciona una estructura genérica para
 construir sistemas deductivos con un especial foco en la prueba de
 teoremas de lógica de orden superior. Sin embargo, Isar proporciona un
 entorno de lenguaje propio, diseñado específicamente para el desarrollo
de pruebas y teorias. En su conjunto Isabelle/Isar es un marco de
 referencia para el desarrollo formal de documentos matemáticos
 incluyendo una comprobación completa de pruebas, en el que las
 definiciones y pruebas se organizan como teorias. 
En nuestro caso el sistema de pruebas automático que usaremos es
 Isabelle/HOL que es una especialización de Isabelle/Isar con lógica de
 orden superior(HOL).

El objetivo general de este trabajo es mostrar como se elaboran
 demostraciones formales y estructuradas en Isabelle/HOL. Mostrando la
 capacidad que tiene este sistema de pruebas automáticas en los
 diferentes aspectos de las matemáticas. 

El objetivo específico es estudiar la similitud que se encuentran entre
 las demostraciones en lenguaje natural y las de lenguaje formal en 
 Isabelle/HOL de aspectos básicos de las diferentes teorías de las 
matemáticas.

La metodología utilizada para este trabajo fue seleccionar y probar
 formalmente teoremas en las distintas áreas de las matemáticas de forma
que se muestre la capacidad de Isabelle/HOl en los diferentes ámbitos.
Una vez escogido el teorema para formalizar se ha seguido siempre el 
mismo esquema:
\begin{enumerate}
\item Enunciado del teorema en lenguaje natural.

\item Demostración del teorema en lenguaje natural.

\item Especificación en Isabelle/HOL.

\item Demostración en Isabelle/HOL que visiblemente muestra la similitud
con la prueba en lenguaje natural.

\end{enumerate}

Tanto para la demostración formal como para su anterior especificación
 ha sido necesario usar diferentes teorías ya predefinidas en
 Isabelle/HOl e incluso en algunos casos definir una seríe de lemas y
 definiciones para poder llegar a entender y demostrar formalmente el
 teorema. La descripción de los capítulos es la siguiente.


\<close>

(*<*)
end
(*>*)