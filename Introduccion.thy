
(*<*) 
theory Introduccion
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*) 


text \<open>
El razonamiento automático es una de las áreas de las ciencias de la
 computación dedicado principalmente a la creación de programas de forma
que se le dote a un ordenador la capacidad de razonar de una manera
 autónoma. Dentro de este campo, podemos encontrar el subcampo de la
 deducción automatizada que es el que se encarga de la demostración de
 teoremas matemáticas mediante programas de ordenador. Para la
 demostración de teoremas matemáticos es necesario implementar una serie
de información previamente para la posterior formalización de teoremas.
 Luego la formalización de teoremas es el primer paso a la hora del
 razonamiento automático, es decir, poder \textit{"traducir"} teoremas
 matemáticos en un ordenador. El estudio de la formalización comenzó con
los trabajos de Hilbert, Tarski, Neumann, Russell, Turing y Herbrand
 entre otros. Dentro de estos grandes matemáticos, Hilbert se puede
 considerar como uno de los fundadores del formalismo moderno; su
 objetivo fue la construcción axiomática de la totalidad de las
 matemáticas a través de los números naturales y asumiendo que con el 
uso de axiomas no es necesario definir objetos. 


Actualmente el gran interés de la formalización matemática es la
 capacidad de la verificación de demostraciones mediante un ordenador.
Para ello, hay que dotar al ordenador de una información previa al
 teorema y junto con una orientación humana se pueda llegar a validar la
demostración de los teoremas. La importancia que se le atribuye a la
 formalización es la capacidad de cálculos y razonamientos que puede
 realizar un ordenador a la vez, incluso demostrando teoremas muy
 difíciles como el teorema de los Knaster-Tarski. 

Dentro de los sistemas de pruebas automáticas los más usados son HOL,
 Mizar, PVS, Coq, Isabelle/Isar entre otros. Isabelle es un asistente de
prueba genérico, permitiendo expresar en lenguaje formal fórmulas
 matemáticas y proporcionando para probar esas fórmulas a través de
 cálculos lógicos. La instancia más extendida de Isabelle actualmente es
Isabelle/HOL, que proporciona pruebas de teorema de lógica de orden
 superior.

El objetivo general de este trabajo es mostrar como se elaboran
 demostraciones formales y estructuradas en Isabelle/HOL. Mostrando la
 capacidad que tiene este sistema de pruebas automáticas en los
 diferentes aspectos de las matemáticas. 

El objetivo específico es estudiar la similitud que se encuentran entre
 las demostraciones en lenguaje natural y las de Isabelle/HOL de
 aspectos básicos de las diferentes teorías de las matemáticas.

La metodología utilizada para este trabajo fue seleccionar y probar
 formalmente teoremas en las distintas áreas de las matemáticas de forma
que se muestre la capacidad de Isabelle/HOl en los diferentes ámbitos.
 Para la demostración formal se ha necesitado usar diferentes teorías ya
 predefinidas en Isabelle/HOL e incluso en algunos casos definir una 
serie de lemas y definiciones para llegar al objetivo final, demostrar
 formalmente un teorema. La descripción de los capítulos es la
 siguiente.


\<close>

(*<*)
end
(*>*)