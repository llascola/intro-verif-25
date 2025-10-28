module Clase07.WP

open FStar.Mul

type var = string
type state = var -> int
type cond = state -> prop

type expr =
  | Var   : var -> expr
  | Const : int -> expr
  | Plus  : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq    : expr -> expr -> expr
  | Lt    : expr -> expr -> expr
  | Not   : expr -> expr

noeq
type stmt =
  | Assign : var -> expr -> stmt
  | IfZ    : expr -> stmt -> stmt -> stmt
  | Seq    : stmt -> stmt -> stmt
  | Skip   : stmt
  | While  : inv:cond -> expr -> stmt -> stmt

let rec eval_expr (s : state) (e : expr) : int =
  match e with
  | Var x -> s x
  | Const n -> n
  | Plus e1 e2 -> eval_expr s e1 + eval_expr s e2
  | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
  | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
  | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2 then 0 else 1
  | Lt e1 e2 -> if eval_expr s e1 < eval_expr s e2 then 0 else 1
  | Not e -> if eval_expr s e = 0 then 1 else 0

let override (#a:eqtype) (#b:Type) (f : a -> b) (x:a) (y:b) : a -> b =
  fun z -> if z = x then y else f z

noeq
type runsto : (s0:state) -> (p:stmt) -> (s1:state) -> Type u#1 =
  | R_Skip : s:state -> runsto s Skip s
  | R_Assign : s:state -> x:var -> e:expr -> runsto s (Assign x e) (override s x (eval_expr s e))
  | R_Seq :
    #p:stmt -> #q:stmt ->
    #s:state -> #t:state -> #u:state ->
    runsto s p t ->
    runsto t q u ->
    runsto s (Seq p q) u
  | R_IfZ_True :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto s t s' ->
    squash (eval_expr s c == 0) ->
    runsto s (IfZ c t e) s'
  | R_IfZ_False :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto s e s' ->
    squash (eval_expr s c =!= 0) ->
    runsto s (IfZ c t e) s'
  | R_While_True :
    #inv:cond ->
    #c:expr -> #b:stmt -> #s:state -> #s':state -> #s'':state ->
    runsto s b s' ->
    squash (eval_expr s c == 0) ->
    runsto s' (While inv c b) s'' ->
    runsto s  (While inv c b) s''
  | R_While_False :
    #inv:cond -> #c:expr -> #b:stmt -> #s:state ->
    squash (eval_expr s c =!= 0) ->
    runsto s (While inv c b) s

noeq
type hoare : (pre:cond) -> (p:stmt) -> (post:cond) -> Type u#1 =
  | H_Skip : pre:cond -> hoare pre Skip pre
  | H_Seq :
    #p:stmt -> #q:stmt ->
    #pre:cond -> #mid:cond -> #post:cond ->
    hoare pre p mid ->
    hoare mid q post ->
    hoare pre (Seq p q) post

  | H_If :
    #c:expr -> #p:stmt -> #q:stmt -> #pre:cond -> #post:cond ->
    hoare (fun (s:state) -> (pre s) /\ (eval_expr s c = 0)) p post ->
    hoare (fun (s:state) -> (pre s) /\ (eval_expr s c <> 0)) q post ->
    hoare pre (IfZ c p q) post
  
  | H_Assign : 
    #x:var -> #e:expr -> #post:cond ->
    hoare (fun (s:state) -> post (override s x (eval_expr s e))) 
          (Assign x e)
          post

  | H_While :
    #inv':cond -> #c:expr -> #b:stmt ->
    inv:cond ->
    hoare (fun s -> inv s /\ eval_expr s c == 0) b inv ->
    hoare inv (While inv' c b) (fun s -> inv s /\ eval_expr s c =!= 0)

  | H_Weaken :
    #pre:cond -> #p:stmt -> #post:cond ->
    pre':cond -> post':cond ->
    hoare pre p post ->
    squash (forall x. pre' x ==> pre x) ->
    squash (forall x. post x ==> post' x) ->
    hoare pre' p post'

  | H_Pure :
    #pre:cond -> #p:stmt -> #post:cond ->
    pre0:prop ->
    hoare (fun s -> pre s /\ pre0) p post ->
    hoare (fun s -> pre s /\ pre0) p (fun s -> post s /\ pre0)

// Demostrar que esta regla es admisible, es decir, que
// podemos "asumir" que la tenemos para demostrar, pero no
// necesitamos analizarla cuando destruímos una prueba:
//
// | R_While :
//   #c:expr -> #b:stmt ->
//   #s:state -> #s':state ->
//   runsto (IfZ c (Seq b (While c b)) Skip) s s' ->
//   runsto (While c b) s s'
let r_while (#inv:cond) (#c:expr) (#b:stmt) (#s #s' : state)
            (pf : runsto s (IfZ c (Seq b (While inv c b)) Skip) s')
  : runsto s (While inv c b) s'
= match pf with
  | R_IfZ_False skip sq  -> R_While_False sq 
  | R_IfZ_True seqbw sq  -> 
    match seqbw with
    | R_Seq b w -> R_While_True b sq w


// Por alguna razón acá no me deja probar por casos en stmt
let rec hoare_ok (p:stmt) (#pre:cond) (#post:cond) (#s0 #s1 : state) (pf : hoare pre p post) (e_pf : runsto s0 p s1) 
  : Lemma (requires pre s0)
          (ensures  post s1)
= match pf with
  | H_Skip _ -> ()
  | H_Assign -> ()
  | H_Seq pfr pfs -> 
    let Seq r s = p in
    let R_Seq e_r e_s = e_pf in
      hoare_ok r pfr e_r;
      hoare_ok s pfs e_s
  | H_If pft pff  ->
    let IfZ e r s = p in 
    (match e_pf with
    | R_IfZ_True e_t _ -> hoare_ok r pft e_t
    | R_IfZ_False e_f _ -> hoare_ok s pff e_f)
  | H_While inv bpf  ->
    let While inv e b = p in
    (match e_pf with
    | R_While_False _ -> ()
    | R_While_True r_b v r_w ->
      hoare_ok b bpf r_b;
      hoare_ok p pf r_w)
  | H_Weaken _ _ pf' _ _  -> 
    hoare_ok p pf' e_pf
  | H_Pure _ pf' -> 
    hoare_ok p pf' e_pf

type wp = cond -> cond

let hoare_strengthen_pre (pre pre' : cond) (p:stmt) (post:cond)
    (_ : squash (forall x. pre' x ==> pre x))
    (pf : hoare pre p post)
  : hoare pre' p post
  = H_Weaken pre' post pf () ()

let hoare_weaken_post (pre:cond) (p:stmt) (post post' : cond)
    (_ : squash (forall x. post x ==> post' x))
    (pf : hoare pre p post)
  : hoare pre p post'
  = H_Weaken pre post' pf () ()

(* Cómputo de WPs *)

let assign_wp (x:var) (e:expr) : wp =
  fun (c: cond) ->
    fun s -> c (override s x (eval_expr s e)) 

let ite_wp (c:expr) (wp_t wp_e : wp) : wp =
  fun (con: cond) ->
    fun s -> 
      match eval_expr s c with
      | 0 -> (wp_t con) s
      | _ -> (wp_e con) s

let seq_wp (wpp wpq: wp) : wp =
  fun cond -> wpq cond |> wpp

let while_wp (inv:cond) (c:expr) (wp_b:wp) : wp =
  fun post s ->
    inv s
    /\ (forall s. eval_expr s c == 0 /\ inv s ==> wp_b inv s)  // invariante es induc
    /\ (forall s'. inv s' /\ eval_expr s' c =!= 0 ==> post s') // al finalizar implica post

let rec cwp (p:stmt) : wp =
  match p with
  | Assign x e -> assign_wp x e
  | Skip -> id
  | Seq p q -> seq_wp (cwp p) (cwp q)
  | IfZ c t e -> ite_wp c (cwp t) (cwp e)
  | While inv c b -> while_wp inv c (cwp b)

(* Correctitud de WPs *)
let rec cwp_ok (p:stmt) (post : cond)
  : (hoare (cwp p post) p post)
  = match p with
    | Skip -> H_Skip post
    | Assign x e ->
      let pf: hoare (fun s -> post (override s x (eval_expr s e))) p post = H_Assign #x #e in 
      H_Weaken (cwp p post) post pf () ()
    | Seq p q ->
      let hi_q : hoare (cwp q post) q post = cwp_ok q post in
      let hi_p : hoare (cwp p (cwp q post)) p (cwp q post) = cwp_ok p (cwp q post) in
      H_Seq hi_p hi_q
    | IfZ c t e ->
      let wpt : cond = cwp t post in
      let wpe : cond = cwp e post in
      let hi_t : hoare wpt t post = cwp_ok t post in
      let hi_e : hoare wpe e post = cwp_ok e post in
      let pre_t : cond = (fun s -> (cwp p post) s /\ (eval_expr s c = 0)) in
      let pre_e : cond = (fun s -> (cwp p post) s /\ (eval_expr s c <> 0)) in
      let w_t : hoare pre_t t post = 
        H_Weaken pre_t post hi_t () () in
      let w_e : hoare pre_e e post =
        H_Weaken pre_e post hi_e () () in
      H_If #c w_t w_e
    | While inv c b ->
      let wp_b = cwp b in
      let pf_b : hoare (wp_b inv) b inv = cwp_ok b inv in
      let inv_is_inductive : prop = forall s. inv s /\ eval_expr s c == 0 ==> wp_b inv s in
      let implies_post : prop = forall s'. inv s' /\ eval_expr s' c =!= 0 ==> post s' in
      let pf_b : hoare (fun s -> (inv s /\ (inv_is_inductive /\ implies_post)) /\ eval_expr s c == 0)
                       b
                       (fun s -> inv s /\ (inv_is_inductive /\ implies_post))
      =
        H_Pure #(fun s -> inv s /\ eval_expr s c == 0) #b #inv
          (inv_is_inductive /\ implies_post) (
          hoare_strengthen_pre
            (wp_b inv)
            (fun s -> inv s /\ eval_expr s c == 0 /\ (inv_is_inductive /\ implies_post))
            b
            inv
            ()
            pf_b)
        |> hoare_strengthen_pre _ _ _ _ ()
      in
      let pf0 : hoare (fun s -> inv s /\ (inv_is_inductive /\ implies_post))
                      (While inv c b)
                      (fun s -> inv s /\ (inv_is_inductive /\ implies_post) /\ eval_expr s c =!= 0)
      =
        H_While #inv #c #b (fun s -> inv s /\ (inv_is_inductive /\ implies_post)) pf_b
      in
      let pf1 : hoare (while_wp inv c (cwp b) post)
                      (While inv c b)
                      post
      =
        H_Weaken _ _ pf0 () ()
      in
      pf1

(* Agregar 1 a x. *)
let add1 =
  Assign "x" (Plus (Var "x") (Const 1))
let wp_add1 : wp = cwp add1
let _ = assert (forall s. s "x" = 10 <==> wp_add1 (fun s -> s "x" = 11) s)
(* DESCOMENTAR *)
(* Arriba garantizamos que la WP para x=11 es x=10. Debería andar luego de completar
definiciones. *)

(* Agregando 2 a x, mediante y. *)
let add2 =
  Assign "y" (Plus (Var "x") (Const 1)) `Seq`
  Assign "x" (Plus (Var "y") (Const 1))
let wp_add2 : wp = cwp add2
let _ = assert (forall s. s "x" = 10 <==> wp_add2 (fun s -> s "x" = 12) s)
(* Encontrar la WP para la postcondición x=12. ¿Qué pasa con y? *)
(* y puede tener cualquier valor, ya que al hacer y := x + 1, su valo anterior
no tiene más sentido dentro de la post condición.*)

(* Intercambiando dos variables via una tercera. *)
let swap : stmt =
  Assign "t" (Var "x") `Seq`
  Assign "x" (Var "y") `Seq`
  Assign "y" (Var "t")
let wp_swap : wp = cwp swap
(* Demuestre que el programa intercambia x e y, demostrando un teorema sobre
la WP *paramétrico* sobre x e y. *)
let _ = assert (forall s x0 y0. s "x" = x0 /\ s "y" = y0  <==> wp_swap (fun s -> s "x" = y0 /\ s "y" = x0) s)

(* Opcional: escriba el programa siguiente
     x = x + y;
     y = x - y;
     x = x - y;
  y demuestra que también intercambia los valores de x e y. *)

let swap2 : stmt =
  Assign "x" (Plus (Var "x") (Var "y")) `Seq`
  Assign "y" (Minus (Var "x") (Var "y")) `Seq`
  Assign "x" (Minus (Var "x") (Var "y"))

let wp_swap2 : wp = cwp swap2
let _ = assert (forall s x0 y0. s "x" = x0 /\ s "y" = y0  <==> wp_swap2 (fun s -> s "x" = y0 /\ s "y" = x0) s)


(* Mover x a y. *)

let move_x_y : stmt =
  (* y := 0;
     while (y < x)
       y := y + 1 *)
  Assign "y" (Const 0) `Seq`
  While 
    (fun s -> s "x" >= s "y") // invariante
    (Lt (Var "y") (Var "x"))
    (Assign "y" (Plus (Var "y") (Const 1)))
let wp_move_x_y : wp = cwp move_x_y
let pre_move = wp_move_x_y (fun s -> s "x" == s "y")
(* Encuentre la WP para la postcondición x=y. *)
let _ = assert (forall s. s "x" >= 0 <==> pre_move s)

let move_x_y_ok :
  hoare (fun s -> s "x" >= 0) move_x_y (fun s -> s "y" = s "x")
= hoare_strengthen_pre  _ _ _ _ () <| cwp_ok move_x_y (fun s -> s "y" = s "x")
(* Armando una tripleta a partir del lema anterior. Esto puede hacerse para
cada uno de los programas anteriores. Descomentar, debería andar. *)

(* Cuenta regresiva. Encuentre la WP para la postcondición x=0. ¿Cuál invariante debe usar? *)
let countdown_inv : cond = fun s -> s "x" >= 0
let countdown : stmt =
  While
    countdown_inv
    (Not (Eq (Var "x") (Const 0)))
    (Assign "x" (Plus (Var "x") (Const (-1))))
let wp_countdown : wp = cwp countdown
let pre_countdown = wp_countdown (fun s -> s "x" == 0)
let _ = assert (forall s. s "x" >= 0 <==> pre_countdown s)

let rec monotonia (p:stmt) (q1 q2 : cond)
  : Lemma (requires forall s. q1 s ==> q2 s)
          (ensures forall s. cwp p q1 s ==> cwp p q2 s)
  = match p with
    | Assign x e -> ()
    | Skip -> ()
    | Seq p q -> 
      monotonia q q1 q2;
      monotonia p (cwp q q1) (cwp q q2)
    | IfZ c t e ->
      monotonia t q1 q2;
      monotonia e q1 q2
    | While inv c b ->
      monotonia b q1 q2
