module Clase01

(* Hace que '*' sea la multiplicación de enteros, en vez del constructor de tuplas. *)
open FStar.Mul

let suma (x y : int) : int = x + y

(* Defina una función suma sobre naturales *)
let addnat (x y : nat) : nat = suma x y

(* Defina una función suma de 3 argumentos, que use la anterior. *)
let suma3 (x y z : int) : int = suma x (suma y z)

(* Defina una función que incremente un número en 1. *)
let incr (x:int) : int = x + 1

(* Dé más tipos a la función de incremento. ¿Cómo se comparan
estos tipos? *)
let incr'   (x:nat) : int = incr x
let incr''  (x:nat) : nat = incr x
let incr''' (x:nat) : y:int{y = x+1} = incr x

(* Un tipo refinado es un subtipo del tipo base, se puede
usar sin coerción. El subtipado es también consciente de funciones. *)
let addnat' (x y : nat) : int = x + y

let debilitar1 (f : int -> int) : nat -> int = f
let debilitar2 (f : nat -> nat) : nat -> int = f
let debilitar3 (f : int -> nat) : nat -> int = f

let par   (x:int) : bool = x % 2 = 0
let impar (x:int) : bool = x % 2 = 1

(* Dadas estas definiciones, dé un tipo a incr que diga
que dado un número par, devuelve un número impar. *)
 let incr'''' (x:int{par x}) : y:int{impar y} = x+1

(* ¿Por qué falla la siguiente definición? Arreglarla. *)
// El atributo expect_failure causa que F* chequeé que la definición
// subsiguiente falle. Borrarlo para ver el error real.
let muldiv (a b : int{b <> 0}) : y:int{y = a} = (a * b) / b

(* Defina una función de valor absoluto *)
let abs (x:int) : nat = 
   if x < 0 then -x else x

(* Defina una función que calcule el máximo de dos enteros. *)
let max (x y : int) : int = 
   if x < y then y else x

(* Dé tipos más expresivos a max.
   1- Garantizando que el resultado es igual a alguno de los argumentos
   2- Además, garantizando que el resultado es mayor o igual a ambos argumentos. *)
let max' (x y : int) : z:int{z = x || z = y} = max x y 

let max'' (x y : int) : (z : int {x <= z && y <= z}) = max' x y 

(* Defina la función de fibonacci, de enteros a enteros,
o alguna restricción apropiada. *)

let rec fib (x:nat) : y:pos{x <= y} =
   match x with
   | 0 -> 1
   | 1 -> 1
   | n -> fib(x-1) + fib(x-2)

(* Defina un tipo 'digito' de naturales de un sólo dígito. *)
type digito = x:nat{x <= 9}

(* Defina una función que compute el máximo de tres dígitos, usando
alguna definición anterior. El resultado debe ser de tipo digito.
¿Por qué funciona esto? ¿De cuáles partes anteriores del archivo
depende, exactamente? *)
let max_digito (x y z : digito) : digito = max'' x (max'' y z)
(*
   Funciona ya que max'' está definida a partir de max' cuyo resultado ganarantiza
   que el resultado sea x o y o z, los cuales son dígitos, por lo cual el resultado
   de max_digito es un digito

*)

(* Defina la función factorial. ¿Puede darle un mejor tipo? *)
let rec fac (x:nat) : pos =
   match x with
   | 0 -> 1
   | n -> n * fac(n-1)

(* Defina una función que sume los números naturales de 0 a `n`. *)

let rec triang (n:nat) : nat = 
   if n = 0 then 0 else n + (triang (n-1))

(* Intente darle un tipo a fib que diga que el resultado es siempre
mayor o igual al argumento. Si el chequeo falla, dé hipótesis de por qué. *)
let rec fib' (x:nat) : n:nat{x <= n} = //Tipo interesante
   match x with
   | 0 -> 1
   | 1 -> 1
   | 2 -> 2
   | n -> fib'(x-1) + fib'(x-2) 
(*
Tenemos
   fib'(x) = fib'(x-1) + fib'(x-2)
     >= (x - 1) + (x - 2)
     = 2x - 3
Por lo cual los casos 0, 1 y 2 deben estar contemplados en el patter matching
para que el solver pueda probar el tipo
*)


(* Idem para la función factorial. *)
let fac' (x:nat) : n:nat{x <= n} = fac x

(* Defina la siguiente función que suma una lista de enteros. *)
val sum_int : list int -> int
let rec sum_int xs = 
   match xs with
   | [] -> 0
   | n::s -> n + sum_int s

(* Defina la siguiente función que revierte una lista de enteros. *)
let rec rev_aux (ys zs: list int) : Tot (list int) (decreases zs) =
   match zs with
   | [] -> ys
   | n::s -> rev_aux (n::ys) s

val rev_int : list int -> list int
let rev_int xs = rev_aux [] xs // O(n), n = len xs