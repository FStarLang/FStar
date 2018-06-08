module Indind

/// Induction-induction can be encoded in F* at least up to simple
/// elimination (see Forsberg ...)
/// In this file we show how to define the following type
/// of list of natural numbers whose last element is Z

/// We would like to define the following type in pseudo-fstar syntax
(* type vdl : Type0 = *)
(*   | Nil : vdl *)
(*   | Cons : tail:vdl -> content tail -> vdl *)

(* and content : vdl -> Type0 = *)
(*   | Z : content Nil *)
(*   | S : #l:vdl -> x:content l -> content (Cons x l) *)

/// but we currently don't support mutual inductive indexed
/// on each other, so we start by defining mutual inductive
/// without indexing

type vdl0 : Type0 =
  | Nil : vdl0
  | Cons : tail:vdl0 -> content0 -> vdl0

and content0 : Type0 =
  | Z : content0
  | S : l:vdl0 -> x:content0 -> content0

/// Then we define predicates by recursion, carving out the
/// valid elements of the indexing

let rec vdl_valid (l:vdl0) : Tot Type0 (decreases l) = match l with
  | Nil -> True
  | Cons tl x -> content_valid tl x

and content_valid (l:vdl0) (x:content0) : Tot Type0 (decreases x) = match x with
 | Z -> l == Nil
 | S tl x -> vdl_valid tl /\ content_valid tl x /\ l == Cons tl x

/// The types we wanted to define are the refinement of the un-indexed
/// inductives with the validity predicates

let vdl = v:vdl0{vdl_valid v}
let content (l:vdl) = c:content0{content_valid l c}

/// We then derive the corresponding induction schemes

let rec vdl_induction (p: vdl -> Tot Type0)
                      (q: (v:vdl -> content v -> Tot Type0))
                      (hNil:p Nil)
                      (hCons: (tl:vdl -> p tl -> x:content tl -> q tl x -> Tot (p (Cons tl x))))
                      (hZ : q Nil Z)
                      (hS : (l:vdl -> p l -> x:content l -> q l x -> Tot (q (Cons l x) (S l x))))
                      (v:vdl)
                      : Tot (p v)
 = match v with
 | Nil -> hNil
 | Cons tl x -> hCons tl (vdl_induction p q hNil hCons hZ hS tl) x (content_induction p q hNil hCons hZ hS tl x)

and content_induction (p: vdl -> Tot Type0)
                      (q: (v:vdl -> content v -> Tot Type0))
                      (hNil:p Nil)
                      (hCons: (tl:vdl -> p tl -> x:content tl -> q tl x -> Tot (p (Cons tl x))))
                      (hZ : q Nil Z)
                      (hS : (l:vdl -> p l -> x:content l -> q l x -> Tot (q (Cons l x) (S l x))))
                      (l:vdl) (x:content l)
                      : Tot (q l x)
  = match x with
  | Z -> hZ
  | S tl x -> hS tl (vdl_induction p q hNil hCons hZ hS tl) x (content_induction p q hNil hCons hZ hS tl x)

/// Another example to model the syntax of types of Dependent Type Theory
/// (note that we would need/it would be easier with Induction Recursion
/// to give a semantic to such a syntax)

/// ⊢ Γ ctx
(* type ctx : Type0 = *)
(*   | EmptyCtx : ctx *)
(*   | ConxCtx : g:ctx -> a:valid_typ g -> ctx *)

/// Γ ⊢ A type
(* and valid_typ : ctx -> Type0 = *)
(*   | Unit : g:ctx -> valid_typ g *)
(*   | Bool : g:ctx -> valid_typ g *)
(*   | Prod : g:ctx -> a:valid_typ g -> b:valid_typ (ConsCtx g a) -> valid_typ g *)
(*   | U : g:ctx -> valid_typ g *)
(*   | Var : g:ctx -> u_mem g -> valid_typ g *)

/// positions in context Γ
(* and u_mem : ctx -> Type0 = *)
(*   | UHere : g:ctx -> u_mem (ConxCtx g (U g)) *)
(*   | UNext : g:ctx -> a:valid_typ g -> u_mem g -> u_mem (ConxCtx g a) *)

/// We start by defining the unindexed mutual inductive

type ctx0 : Type0 =
  | EmptyCtx : ctx0
  | ConsCtx : g:ctx0 -> a:valid_typ0 -> ctx0

and valid_typ0 : Type0 =
  | Unit : g:ctx0 -> valid_typ0
  | Bool : g:ctx0 -> valid_typ0
  | Prod : g:ctx0 -> a:valid_typ0 -> b:valid_typ0 -> valid_typ0
  | U : g:ctx0 -> valid_typ0
  | Var : g:ctx0 -> u_mem0 -> valid_typ0

and u_mem0 : Type0 =
  | UHere : g:ctx0 -> u_mem0
  | UNext : g:ctx0 -> a:valid_typ0 -> u_mem0 -> u_mem0

/// Then the validity predicate

let rec ctx_valid (g0:ctx0) : Tot Type0 (decreases g0) =
  match g0 with
  | EmptyCtx -> True
  | ConsCtx g a -> ctx_valid g /\ valid_typ_valid a g

and valid_typ_valid (a:valid_typ0) (g0:ctx0) : Tot Type0 (decreases a)=
  match a with
  | Unit g -> g0 == g /\ ctx_valid g
  | Bool g -> g0 == g /\ ctx_valid g
  | Prod g a b -> g0 == g /\ ctx_valid g /\ valid_typ_valid a g /\ valid_typ_valid b (ConsCtx g a)
  | U g -> g0 == g /\ ctx_valid g
  | Var g w -> g0 == g /\ ctx_valid g /\ u_mem_valid w g

and u_mem_valid (w:u_mem0) (g0:ctx0) : Tot Type0 (decreases w) =
  match w with
  | UHere g -> g0 == ConsCtx g (U g) /\ ctx_valid g
  | UNext g a w -> g0 == ConsCtx g a /\ ctx_valid g /\ valid_typ_valid a g /\ u_mem_valid w g

/// And finally the types

let ctx = g:ctx0{ctx_valid g}
let valid_typ (g:ctx) = a:valid_typ0{valid_typ_valid a g}
let u_mem (g:ctx) = w:u_mem0{u_mem_valid w g}

/// We redefine constructors to be in the corresponding carved-out types

let empty_ctx : ctx = EmptyCtx
let cons_ctx (g:ctx) (a:valid_typ g) : ctx = ConsCtx g a

let unit (g:ctx) : valid_typ g = Unit g
let bool (g:ctx) : valid_typ g = Bool g
let prod (g:ctx) (a:valid_typ g) (b:valid_typ (cons_ctx g a)) : valid_typ g = Prod g a b
let u (g:ctx) : valid_typ g = U g
let var (g:ctx) (w:u_mem g) : valid_typ g = Var g w

let u_here (g:ctx) : u_mem (cons_ctx g (u g)) = UHere g
let u_next (g:ctx) (a:valid_typ g) (w:u_mem g) : u_mem (cons_ctx g a) = UNext g a w

/// And a simple example to derive (⊢ Π(A: U)A Type)

let t : valid_typ empty_ctx =
  let g0 = empty_ctx in
  let u0 = u g0 in
  let x = var (cons_ctx g0 u0) (u_here g0) in
  prod g0 u0 x
