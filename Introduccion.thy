
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
 Para ello, es necesario poder expresar las definiciones, teoremas y
 pruebas en un lenguaje generado por una gramática que permita verificar
 de forma mecánica las pruebas. También hay que dotar al ordenador de
 una información previa al teorema y junto con una orientación humana se
 pueda llegar a validar la demostración de los teoremas. La importancia
 que se le atribuye a la formalización es la capacidad de cálculos y
 razonamientos que puede realizar un ordenador a la vez, incluso
 demostrando teoremas muy difíciles como el teorema de los
 Knaster--Tarski como se verá en el Capítulo 5. En \cite{100theorems}
 podemos encontrar una lista de 100 teoremas formalizados junto con el
 programa usado.

 Dentro de los sistemas de pruebas automáticas los más usados como se
 puede ver en \cite{Provers} son HOL, Mizar, PVS, Coq, Isabelle/Isar
 entre otros. Isabelle proporciona una estructura genérica para
 construir sistemas deductivos con un especial foco en la prueba de
 teoremas de lógica de orden superior. Sin embargo, Isar proporciona un
 entorno de lenguaje propio, diseñado específicamente para el desarrollo
 de pruebas y teorias. En su conjunto Isabelle/Isar es un marco de
 referencia para el desarrollo formal de documentos matemáticos
 incluyendo una comprobación completa de pruebas, en el que las
 definiciones y pruebas se organizan como teorias.  En nuestro caso el
 sistema de pruebas automático que usaremos es Isabelle/HOL que es una
 especialización de Isabelle/Isar con lógica de orden superior(HOL).

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
 Isabelle/HOl e incluso en algunos casos introducir una serie de lemas y
 definiciones para poder llegar a entender y demostrar formalmente el
 teorema.

 La descripción de los capítulos es la siguiente.

 Dentro de la gran cantidad de aspectos que podemos encontrar en las
 matemáticas, se ha elegido 5 de ellos que son los que vamos a tratar.

 En el capítulo 1 se muestran dos teoremas de la teoría de números. El
 primero de ellos es un resultado clásico sobre números impares. La
 decisión de escoger este teorema fue debido a su demostración, ya que
 se realiza por inducción sobre los números naturales; pudiendo mostrar
 el esquema inductivo predefinido en Isabelle y observando la gran
 similitud existente entre la demostración en lenguaje natural y formal.
 También se muestra la capacidad de Isabelle/HOL dando pruebas menos
 explícitas e incluso automáticas. El segundo teorema es una propiedad
 sobre los conjuntos finitos de números naturales que al igual que en el
 anterior se demuestra de manera inductiva, pero esta vez una inducción
 sobre conjuntos finitos; mostrando también el esquema ya predefinido en
 Isabelle/HOL de inducción sobre conjuntos finitos.

 En el capítulo 2 podemos encontrar dos resultados de la teoría de
 funciones. Estos son una caracterización sobre funciones inyectivas y
 sobreyectivas respectivamente. La importancía de estos teoremas es
 mostrar la capacidad de Isabelle/HOL a la hora de trabajar con tipos;
 es decir, con los dominios y codominios de las funciones. En la
 demostración de ambos teoremas es necesario especificar los tipos tanto
 de las funciones como de los elementos, debido a que en el caso de no
 especificarlo Isabelle/HOL toma el tipo más general posible y no te
 admite la prueba. También se ha de descatar la necesidad de usar
 definiciones de la teoría ya predefinida
 \href{http://bit.ly/2XuPQx5}{Fun.thy} e introducir unas nuevas para
 conseguir la similitud con la especificación y demostración formal.

 En el capítulo 3 se muestra el teorema de Cantor, un teorema importante
 de la teoría de conjuntos. La elección del teorema fue debido a su
 demostración formal y automática, ya que su demostración formal es
 idéntica a la demostración en lenguaje natural y en cuanto a su
 demostración automática cabe destacar la capacidad de Isabelle/HOL para
 demostrarlo automáticamente.

 En el capítulo 4 se estudia el teorema del punto fijo de Knaster--Tarski
 un resultado de la teoría de retículos. La elección del teorema fue
 el interés en la teoría de retículos, ya que es una teoría importada en
 Isabelle/HOL y para su perfecta comprensión tiene una notación
 específica. Además notar la peculiaridad de los retículos y de los
 retículos completos que se definen en Isabelle/HOL como clases.

 En el capítulo 5 se formaliza la teoría de la geometría, en la que
 diferenciamos tres tipos diferentes: geometría simple, geometría no
 proyectiva y geometría proyectiva. Cada tipo de geometría la
 declararemos en un entorno local definiendo los axiomas propios de ella
 y dentro de él, demostrando una serie de lemas y dando, por último, una
 interpretación del mínimo modelo que se puede formar verificando los
 axiomas.

 Por último cabe destacar el apéndice A, en el que basándonos en el
 \href{http://bit.ly/2OMbjMM}{libro de HOL} mostramos todos las reglas y
 lemas usados en el trabajo agrupándolas en diferentes secciones.

\<close>

(*<*)
end
(*>*)
