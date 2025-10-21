module Clase06.Imp

open FStar.Mul

type var = string

type expr =
  | Var   : var -> expr
  | Const : int -> expr
  | Plus  : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq    : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | IfZ    : expr -> stmt -> stmt -> stmt
  | Seq    : stmt -> stmt -> stmt
  | Skip   : stmt
  | While  : expr -> stmt -> stmt

type state = var -> int

let rec eval_expr (s : state) (e : expr) : int =
  match e with
  | Var x -> s x
  | Const n -> n
  | Plus  e1 e2 -> eval_expr s e1 + eval_expr s e2
  | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
  | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
  | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2 then 0 else 1

let override (#a:eqtype) (#b:Type) (f : a -> b) (x:a) (y:b) : a -> b =
  fun z -> if z = x then y else f z

(* Relación de evaluación big step. *)
noeq
type runsto : (p:stmt) -> (s0:state) -> (s1:state) -> Type0 =
  | R_Skip : s:state -> runsto Skip s s
  | R_Assign : s:state -> #x:var -> #e:expr -> runsto (Assign x e) s (override s x (eval_expr s e))

  | R_Seq :
    #p:stmt -> #q:stmt ->
    #s:state -> #t:state -> #u:state ->
    runsto p s t -> runsto q t u -> runsto (Seq p q) s u

  | R_IfZ_True :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto t s s' ->
    squash (eval_expr s c == 0) ->
    runsto (IfZ c t e) s s'

  | R_IfZ_False :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto e s s' ->
    squash (eval_expr s c <> 0) ->
    runsto (IfZ c t e) s s'

  | R_While_True :
    #c:expr -> #b:stmt -> #s:state -> #s':state -> #s'':state ->
    runsto b s s' ->
    squash (eval_expr s c = 0) ->
    runsto (While c b) s' s'' ->
    runsto (While c b) s s''

  | R_While_False :
    #c:expr -> #b:stmt -> #s:state ->
    squash (eval_expr s c <> 0) ->
    runsto (While c b) s s

// Demostrar que esta regla es admisible, es decir, que
// podemos "asumir" que la tenemos para demostrar, pero no
// necesitamos analizarla cuando destruímos una prueba:
//
// | R_While :
//   #c:expr -> #b:stmt ->
//   #s:state -> #s':state ->
//   runsto (IfZ c (Seq b (While c b)) Skip) s s' ->
//   runsto (While c b) s s'
let r_while (#c:expr) (#b:stmt) (#s #s' : state) (pf : runsto (IfZ c (Seq b (While c b)) Skip) s s')
  : runsto (While c b) s s'
= match pf with
  | R_IfZ_False skip sq  -> R_While_False sq 
  | R_IfZ_True seqbw sq  -> 
    match seqbw with
    | R_Seq b w -> R_While_True b sq w

type cond = state -> bool

noeq
type hoare : (pre:cond) -> (p:stmt) -> (post:cond) -> Type0 =

  | H_Skip : pre:cond -> hoare pre Skip pre // {P} Skip {P}

  | H_Assign : 
    #x:var -> #e:expr -> #post:cond ->
    hoare (fun (s:state) -> post (override s x (eval_expr s e))) 
          (Assign x e)
          post

  | H_Seq : 
    #p:stmt -> #q:stmt ->
    #pre:cond -> #mid:cond -> #post:cond ->
    hoare pre p mid ->
    hoare mid q post ->
    hoare pre (Seq p q) post  // {pre} p {mid} /\ {mid} q {post} ==> {pre} p;q {post} 

  | H_If :
    #c:expr -> #p:stmt -> #q:stmt -> #pre:cond -> #post:cond ->
    hoare (fun (s:state) -> (pre s) && (eval_expr s c = 0)) p post ->
    hoare (fun (s:state) -> (pre s) && (eval_expr s c <> 0)) q post ->
    hoare pre (IfZ c p q) post

  | H_While : 
    #b:stmt -> #c:expr -> #inv:cond ->
    hoare (fun (s:state) -> (inv s) && (eval_expr s c = 0)) b inv ->
    hoare inv (While c b) (fun (s:state) -> (inv s) && (eval_expr s c <> 0))

let st0 : state = fun _ -> 0

let test11 : hoare (fun _ -> true) Skip (fun _ -> true) =
  H_Skip (fun _ -> true)

let test : hoare (fun _ -> true) (Assign "x" (Const 1)) (fun _ -> true) =
  H_Assign 

let test1 : hoare (fun _ -> true) (Assign "x" (Const 1)) (fun s -> s "x" = 1) =
  H_Assign 

// Me salió así por que no tenía ni idea de como conseguir la mid condition
// en H_Seq, y se me ocurrió que el sistema de tipos se puede dar cuenta solo de que
// los tipos coinciden, sin necesidad de pasarle pre, post, s0 y s1.
// Queda medio críptico, pero elegante.
let rec hoare_ok (p:stmt) (#pre:cond) (#post:cond) (pf : hoare pre p post)
                 (#s0 #s1 : state) (e_pf : runsto p s0 s1)
  : Lemma (requires pre s0)
          (ensures  post s1)
= match p with
  | Skip -> ()
  | Assign x e -> ()
  | Seq r s -> 
    let H_Seq pfr pfs = pf in 
    let R_Seq e_r e_s = e_pf in 
      hoare_ok r pfr e_r;
      hoare_ok s pfs e_s
  | IfZ e r s ->
    let H_If pft pff = pf in 
    (match e_pf with
    | R_IfZ_True e_t _ -> hoare_ok r pft e_t
    | R_IfZ_False e_f _ -> hoare_ok s pff e_f)
  | While e b ->
    let H_While bpf = pf in
    (match e_pf with
    | R_While_False _ -> ()
    | R_While_True r_b v r_w ->
      hoare_ok b bpf r_b;
      hoare_ok p pf r_w)

