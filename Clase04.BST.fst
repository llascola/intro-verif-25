module Clase04.BST

open FStar.Mul
open FStar.List.Tot
open Clase04.Listas
let max (x y : int) : int = if x > y then x else y

type bst =
  | L
  | N of bst & int & bst

let rec insert (x: int) (t: bst) : bst =
  match t with
  | L -> N (L, x, L)
  | N (l, y, r) ->
    (* Nota: admite duplicados *)
    if x <= y
    then N (insert x l, y, r)
    else N (l, y, insert x r)

let rec member (x: int) (t: bst) : bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

let rec to_list (t: bst) : list int =
  match t with
  | L -> []
  | N (l, x, r) -> to_list l @ [x] @ to_list r

let rec from_list (l: list int) : bst =
  match l with
  | [] -> L
  | x :: xs -> insert x (from_list xs)

let rec size (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + size l + size r

let rec height (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + max (height l) (height r)

let rec insert_size (x:int) (t:bst) : Lemma (size (insert x t) == 1 + size t) =
  match t with
  | L -> ()
  | N (l, x', r)->
    if x <= x'
    then insert_size x l 
    else insert_size x r

let rec insert_height (x:int) (t:bst)
: Lemma (height (insert x t) <= 1 + height t)
= match t with
  | L -> ()
  | N (l, x', r)->
    if x <= x'
    then insert_height x l 
    else insert_height x r

let rec insert_mem (x:int) (t:bst) : Lemma (member x (insert x t)) =
  match t with
  | L -> ()
  | N (l, x' , r) -> 
  if x = x' then ()
  else if x < x' then insert_mem x l else insert_mem x r
  

(* ¿Puede demostrar también que:
     height t <= height (insert x t)
   ? ¿Cuál es la forma "más fácil" de hacerlo? *)
// let height_lemma (x:nat) (t:bst)
// : Lemma (height t <= height (insert x t)) =
//   insert_height x t;
//   (assert height (insert x t) <= 1 + height t);
//   admit()

let rec height_lemma (x:int) (t:bst)
: Lemma (height t <= height (insert x t))
= match t with 
  | L -> ()
  | N (l,x',r) ->
  if x <= x' 
  then 
    (insert_height x l;
     height_lemma x l) 
  else 
    (insert_height x r;
     height_lemma x r)

let rec extract_min (t: bst) : option (int & bst) =
  match t with
  | L -> None
  | N (L, x, r) -> Some (x, r)
  | N (l, x, r) ->
    match extract_min l with
    | None -> None
    | Some (y, l') -> Some (y, N (l', x, r))

let rec extract_min_lema (t:bst) : 
  Lemma (
    match extract_min t with
    | None -> size t = 0
    | Some (_, t') -> size t - 1 = size t'
  ) = 
  match t with
  | L -> ()
  | N (L, x, r) -> ()
  | N (l, x', r) ->  extract_min_lema l

let delete_root (t: bst) : Pure bst (requires N? t) (ensures fun _ -> True) =
  let N (l, _, r) = t in
  match extract_min r with
  | None -> l
  | Some (x, r') -> N (l, x, r')

let delete_root_lema (t: bst) : Lemma (requires N? t) (ensures size t - 1 = size (delete_root t)) =
  let N(l, _ , r) = t in
    extract_min_lema r


let rec delete (x: int) (t: bst) : bst =
  match t with
  | L -> L
  | N (l, y, r) ->
    if x < y then N (delete x l, y, r)
    else if x > y then N (l, y, delete x r)
    else delete_root t

(* Un poco más difícil. Require un lema auxiliar sobre extract_min:
declárelo y demuéstrelo. Si le parece conveniente, puede modificar
las definiciones de delete, delete_root y extract_min. *)
let rec delete_size (x:int) (t:bst) : Lemma (delete x t == t \/ size (delete x t) == size t - 1) =
  match t with
  | L -> ()
  | N (l, x', r)->
    if x < x' then delete_size x l 
    else if x > x' then delete_size x r
    else delete_root_lema t


(* Versión más fuerte del lema anterior. *)
let rec delete_size_mem (x:int) (t:bst)
: Lemma (requires member x t)
        (ensures size (delete x t) == size t - 1)
= match t with
  | L -> ()
  | N (l, x', r)->
    if x < x' then delete_size_mem x l 
    else if x > x' then delete_size_mem x r
    else delete_root_lema t

let rec to_list_length (t:bst) : Lemma (length (to_list t) == size t) =
  match t with
  | L -> ()
  | N (l, x', r) ->
  to_list_length l;
  to_list_length r;
  len_append (to_list l) [x']

(*
  ¿Es cierto que `member x (insert y (insert x t))`? ¿Cómo se puede probar?

  Si, se puede demostrar ya que una especificación de member 
  es que si x =!= y entonces 

    member x (insert y t) = member x t
  
    por lo que resulta facil de probar a partir de esto y el elma insert_mem
    ya que estamos lo probamos
*)
let rec member_insert (t : bst) (x y : int) : 
  Lemma (requires x =!= y) 
        (ensures member x (insert y t) = member x t)
= match t with
  | L -> ()
  | N (l, x', r) ->
    member_insert l x y;
    member_insert r x y

let lemma_a (t : bst) (x y :int) : Lemma (ensures member x (insert y (insert x t)))
= if x = y
  then (insert_mem x (insert x t))
  else (member_insert (insert x t) x y;
       insert_mem x t)

(*
  ¿Es cierto que `delete x (insert x t) == t`?
  No, el tema son los duplicados, por ejemplo

  (insert 3 (insert 4 L))
  
  nos da un arbol de la forma

          4
  t =    /
        3

  Ahora (insert 4 t)

          4
         /
  t' =  3
         \
          4

  Finalmente delete 4

        3
         \
          4

  y claramente 

        3   3
       /  y  \
      4       4

  son distintos para la estructura bst
*)