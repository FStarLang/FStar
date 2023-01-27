module Divergence
open FStar.List.Tot
module L = FStar.List.Tot
open FStar.Mul

//SNIPPET_START: collatz$
(* You can program a function to compute Collatz sequences
   ... though no one knows if it actually terminates for all n *)
let rec collatz (n:pos)
  : Dv (list pos)
  = if n = 1 then [n]
    else if n % 2 = 0
    then n::collatz (n / 2)
    else n::collatz (3 * n + 1)
//SNIPPET_END: collatz$

//SNIPPET_START: loop$
let rec loop (): Dv unit = loop ()
//SNIPPET_END: loop$

//SNIPPET_START: val collatz_ends_in_one$
let last #a (l:list a { Cons? l }) : a = L.index l (L.length l - 1)
val collatz_ends_in_one (n:pos)
  : Dv (l:list pos { Cons? l /\ last l == 1 })
//SNIPPET_END: val collatz_ends_in_one$

//SNIPPET_START: collatz_ends_in_one$
let rec collatz_ends_in_one (n:pos)
  : Dv (l:list pos { Cons? l /\ last l == 1 })
  = if n = 1 then [n]
    else if n % 2 = 0
    then n::collatz_ends_in_one (n / 2)
    else n::collatz_ends_in_one (3 * n + 1)
//SNIPPET_END: collatz_ends_in_one$

//SNIPPET_START: loop_false$
let rec dv_false () : Dv False = dv_false()
//SNIPPET_END: loop_false$

//SNIPPET_START: loop_false_failures$
[@@expect_failure]
let tot_false : Tot False = dv_false()
[@@ expect_failure]
let bad_zero : Tot (y:int{y == 0}) = dv_false (); 1
//SNIPPET_END: loop_false_failures$

[@@ expect_failure]
let rec decr (x:int) : Dv nat = if x = 0 then -1 else decr (x - 1)

//SNIPPET_START: collatz_spec$
let rec collatz_spec (n:pos) (l:list pos)
  : Tot bool (decreases l) 
  = match l with
    | [] -> false
    | hd :: tl -> 
      hd = n && (
        if hd = 1 then tl = []
        else if n%2 = 0 then collatz_spec (n/2) tl
        else collatz_spec (3*n + 1) tl
      )
// collatz' may loop forever on some inputs
// but if it completes it always returns a valid
// Collatz sequence
let rec collatz' (n:pos)
  : Dv (l:list pos { collatz_spec n l } )
  = if n = 1 then [n]
    else if n % 2 = 0
    then n::collatz' (n / 2)
    else n::collatz' (3 * n + 1)

// here's another bogus implementation that always loops
let rec collatz'' (n:pos)
  : Dv (l:list pos { collatz_spec n l } )
  = collatz'' n
//SNIPPET_END: collatz_spec$

//SNIPPET_START: nonpos$
noeq
type nonpos =
  | NonPos : (nonpos -> Dv False) -> nonpos

let loop_nonpos' (f:nonpos) : Dv False =
   let NonPos g = f in g f 
   
let loop_nonpos () : Dv False  = loop_nonpos' (NonPos loop_nonpos')
//SNIPPET_END: nonpos$  

//SNIPPET_START: universe_dv$
let tot_type : Type u#(a + 1) = unit -> Tot (Type u#a)
let dv_type : Type0 = unit -> Dv (Type u#a)
//SNIPPET_END: universe_dv$

(* Or you can program an interpreter for the untyped
   lambda calculus, even though it can express non-terminating
   computations *)

(* A deep embedding of untyped lambda calculus *)

//SNIPPET_START: deep_embedding_syntax$
let var = nat
type term = 
  | Var  : var -> term
  | Int  : int -> term
  | Lam  : term -> term
  | App  : term -> term -> term
//SNIPPET_END: deep_embedding_syntax$

//SNIPPET_START: deep_embedding_subst$
let rec subst (x:var) (v:term) (t:term)
  : Tot term  (decreases t) = 
  match t with
  | Var y -> if x = y then v else t
  | Int _ -> t
  | Lam t -> Lam (subst (x + 1) v t)
  | App t0 t1 -> App (subst x v t0) (subst x v t1)
//SNIPPET_END: deep_embedding_subst$

//SNIPPET_START: deep_embedding_interpreter$
(* This interpreter can (intentionally) loop infinitely *)
let rec interpret (t:term)
  : Dv (option term)
  = match t with
    | Var _
    | Int _
    | Lam _ -> Some t
    | App t0 t1 ->
      let head = interpret t0 in
      match head with
      | None -> None
      | Some (Lam body) -> interpret (subst 0 t1 body)
      | _ -> None //type error, expected a function

(* (\x. x x) (\x. x x) *)
let loops () : Dv _ = interpret (App (Lam (App (Var 0) (Var 0)))
                                     (Lam (App (Var 0) (Var 0))))
//SNIPPET_END: deep_embedding_interpreter$

(* Dv can also be mixed with recursive type definitions, e.g., 
   to give a a denotation for untyped lambda terms
   (Illustrating the interaction of Dv with recursive types &
    lack of positivity requirement) *)
//SNIPPET_START: dyn$    
noeq
type dyn = 
  | DErr  : string -> dyn
  | DInt  : int -> dyn
  | DFun  : (dyn -> Dv dyn) -> dyn
//SNIPPET_END: dyn$    

//SNIPPET_START: denote$    
let ctx_t = nat -> dyn

let shift (ctx:ctx_t) (v:dyn) 
  : ctx_t
  = fun n -> if n = 0 then v else ctx (n - 1)

let rec denote (t:term) (ctx:ctx_t)
  : Dv dyn 
  = match t with
    | Var v -> ctx v
    | Int i -> DInt i
    | Lam t -> DFun (fun v -> denote t (shift ctx v))
    | App t0 t1 -> 
      match denote t0 ctx with
      | DFun f -> f (denote t1 ctx)
      | DErr msg -> DErr msg
      | DInt _ -> DErr "Cannot apply an integer"
//SNIPPET_END: denote$     


(* You can also use dyn for shallowly embedded *)
(* dynamically typed programming, i.e., 
   general-purpose, dynamically typed programming, 
   as in lisp, scheme etc. can be embedded in F* with dyn *)

(* Some convenience constructors for literals *)


//SNIPPET_START: lift_int$
(* Lifting operations on integers to operations on dyn *)
let lift (op: int -> int -> int) (n m:dyn) : dyn
  = match n, m with
    | DInt i, DInt j -> DInt (op i j)
    | _ -> DErr "Expected integers"
let mul = lift op_Multiply
let sub = lift op_Subtraction
let add = lift op_Addition
let div (n m:dyn)
  = match n, m with
    | DInt i, DInt j -> 
      if j = 0 then DErr "Division by zero"
      else DInt (i / j)
    | _ -> DErr "Expected integers"
let mod (n m:dyn)
  = match n, m with
    | DInt i, DInt j -> 
      if j = 0 then DErr "Division by zero"
      else DInt (i % j)
    | _ -> DErr "Expected integers"
//SNIPPET_END: lift_int$

//SNIPPET_START: branch_eq$
(* Branching *)
let if_ (d:dyn) (then_ else_:dyn) =
  match d with
  | DInt b -> 
    if b<>0 then then_ else else_
  | _ -> DErr "Can only branch on integers"

(* comparison *)
let eq_ (d:dyn) (d':dyn)
  : dyn 
  = match d, d' with
    | DInt i, DInt j -> DInt (if i = j then 1 else 0)
    | _ -> DErr "Can only compare integers"
//SNIPPET_END: branch_eq$

//SNIPPET_START: app_fix$
(* Dynamically typed application *)
let app (f:dyn) (x:dyn)
  : Dv dyn
  = match f with
    | DFun f -> f x
    | _ -> DErr "Can only apply a function"
(* general recursion *)
let rec fix (f: (dyn -> Dv dyn) -> dyn -> Dv dyn) (n:dyn)
  : Dv dyn
  = f (fix f) n
//SNIPPET_END: app_fix$

(* Now, a sample program: a dynamically typed factorial
   within our embedded language *)

//SNIPPET_START: collatz_dyn$
(* shorthands *)
let i (i:int) : dyn = DInt i
let lam (f:dyn -> Dv dyn) : dyn = DFun f
(* a dynamically typed analog of collatz *)
let collatz_dyn 
  : dyn 
  = lam (fix (fun collatz n ->
                if_ (eq_ n (i 1))
                    (i 1)
                    (if_ (eq_ (mod n (i 2)) (i 0))
                         (collatz (div n (i 2)))
                         (collatz (add (mul n (i 3)) (i 1))))))
//SNIPPET_END: collatz_dyn$

(* Exercise: Extend `dyn` to include a denotation for lists
   revise collatz_dyn so that it returns a list, similar to the
   collatz at the top of this file *)

//SNIPPET_START: fix_alt$
let rec fix_alt (f: (dyn -> Dv dyn) -> dyn -> Dv dyn) 
  : Dv (dyn -> Dv dyn)
  = f (fix_alt f)
//SNIPPET_END: fix_alt$
