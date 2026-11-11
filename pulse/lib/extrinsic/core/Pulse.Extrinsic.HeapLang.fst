(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Pulse.Extrinsic.HeapLang

(** The deeply embedded source language, before any semantics or logic.
    Context/result indices rule out ill-typed syntax, but references are not
    indexed by allocation or cell kind: those are ownership obligations.

    Binders use typed de Bruijn variables. [rename] moves variables across
    contexts, [subst] replaces them capture-avoidably, and [substitute] performs
    one source let binding. Every body is an AST, never a stored F* callback.
    [context]/[fill] encode left-to-right evaluation positions; their operational
    laws are proved in HeapLang.Semantics. See HeapLang.Notation for readable
    named construction of these same trees. *)

module H = PulseCore.Heap
module L = Pulse.Extrinsic.Language

type ty =
  | TUnit
  | TBool
  | TInt
  | TRef

let value : ty -> Type0 = function
  | TUnit -> unit
  | TBool -> bool
  | TInt -> int
  | TRef -> H.core_ref

type var : list ty -> ty -> Type0 =
  | Here: #g:list ty -> #t:ty -> var (t :: g) t
  | There: #g:list ty -> #t:ty -> #u:ty -> var g t -> var (u :: g) t

noeq
type expr : list ty -> ty -> Type0 =
  | Val: #g:list ty -> #t:ty -> value t -> expr g t
  | Var: #g:list ty -> #t:ty -> var g t -> expr g t
  | Let: #g:list ty -> #a:ty -> #b:ty ->
      expr g a -> expr (a :: g) b -> expr g b
  | If: #g:list ty -> #t:ty ->
      expr g TBool -> expr g t -> expr g t -> expr g t
  | Seq: #g:list ty -> #t:ty -> expr g TUnit -> expr g t -> expr g t
  | Add: #g:list ty -> expr g TInt -> expr g TInt -> expr g TInt
  | Eq: #g:list ty -> expr g TInt -> expr g TInt -> expr g TBool
  | Alloc: #g:list ty -> expr g TInt -> expr g TRef
  | Load: #g:list ty -> expr g TRef -> expr g TInt
  | Store: #g:list ty -> expr g TRef -> expr g TInt -> expr g TUnit
  | Cas: #g:list ty -> expr g TRef -> expr g TInt -> expr g TInt -> expr g TBool
  | NewNode: #g:list ty -> expr g TInt -> expr g TRef -> expr g TRef
  | ReadData: #g:list ty -> expr g TRef -> expr g TInt
  | ReadNext: #g:list ty -> expr g TRef -> expr g TRef
  | WriteNext: #g:list ty -> expr g TRef -> expr g TRef -> expr g TUnit
  | Fork: #g:list ty -> expr g TUnit -> expr g TUnit
  | While: #g:list ty -> expr g TBool -> expr g TUnit -> expr g TUnit

let renaming (g d:list ty) = t:ty -> var g t -> var d t

let lift_renaming (#g #d:list ty) (r:renaming g d) (a:ty)
  : renaming (a :: g) (a :: d)
  = fun t x -> match x with
    | Here -> Here
    | There x -> There (r t x)

let rec rename (#g #d:list ty) (#t:ty) (r:renaming g d) (e:expr g t)
  : Tot (expr d t) (decreases e)
  = match e with
    | Val v -> Val v
    | Var x -> Var (r _ x)
    | Let e body -> Let (rename r e) (rename (lift_renaming r _) body)
    | If c e1 e2 -> If (rename r c) (rename r e1) (rename r e2)
    | Seq e1 e2 -> Seq (rename r e1) (rename r e2)
    | Add e1 e2 -> Add (rename r e1) (rename r e2)
    | Eq e1 e2 -> Eq (rename r e1) (rename r e2)
    | Alloc e -> Alloc (rename r e)
    | Load e -> Load (rename r e)
    | Store e1 e2 -> Store (rename r e1) (rename r e2)
    | Cas e1 e2 e3 -> Cas (rename r e1) (rename r e2) (rename r e3)
    | NewNode e1 e2 -> NewNode (rename r e1) (rename r e2)
    | ReadData e -> ReadData (rename r e)
    | ReadNext e -> ReadNext (rename r e)
    | WriteNext e1 e2 -> WriteNext (rename r e1) (rename r e2)
    | Fork e -> Fork (rename r e)
    | While c body -> While (rename r c) (rename r body)

let substitution (g d:list ty) = t:ty -> var g t -> expr d t

(** Under a new binder, Here must stay bound. Substituted outer expressions
    are weakened so that their free variables cannot be captured. *)
let lift_substitution (#g #d:list ty) (s:substitution g d) (a:ty)
  : substitution (a :: g) (a :: d)
  = fun t x -> match x with
    | Here -> Var Here
    | There x -> rename (fun _ x -> There x) (s t x)

let rec subst (#g #d:list ty) (#t:ty) (s:substitution g d) (e:expr g t)
  : Tot (expr d t) (decreases e)
  = match e with
    | Val v -> Val v
    | Var x -> s _ x
    | Let e body -> Let (subst s e) (subst (lift_substitution s _) body)
    | If c e1 e2 -> If (subst s c) (subst s e1) (subst s e2)
    | Seq e1 e2 -> Seq (subst s e1) (subst s e2)
    | Add e1 e2 -> Add (subst s e1) (subst s e2)
    | Eq e1 e2 -> Eq (subst s e1) (subst s e2)
    | Alloc e -> Alloc (subst s e)
    | Load e -> Load (subst s e)
    | Store e1 e2 -> Store (subst s e1) (subst s e2)
    | Cas e1 e2 e3 -> Cas (subst s e1) (subst s e2) (subst s e3)
    | NewNode e1 e2 -> NewNode (subst s e1) (subst s e2)
    | ReadData e -> ReadData (subst s e)
    | ReadNext e -> ReadNext (subst s e)
    | WriteNext e1 e2 -> WriteNext (subst s e1) (subst s e2)
    | Fork e -> Fork (subst s e)
    | While c body -> While (subst s c) (subst s body)

let substitute (#g:list ty) (#a #b:ty) (v:value a) (body:expr (a :: g) b)
  : expr g b
  = let s : substitution (a :: g) g =
      fun t x -> match x with
      | Here -> Val #g #t v
      | There x -> Var x
    in
    subst s body

let to_val (#g:list ty) (#t:ty) (e:expr g t) : option (value t) =
  match e with
  | Val v -> Some v
  | _ -> None

// Evaluation contexts contain source syntax, not host-language continuations.
noeq
type context : ty -> ty -> Type0 =
  | Hole: #t:ty -> context t t
  | LetCtx: #a:ty -> #b:ty -> #t:ty -> context t a -> expr [a] b -> context t b
  | IfCtx: #a:ty -> #t:ty -> context t TBool -> expr [] a -> expr [] a -> context t a
  | SeqCtx: #a:ty -> #t:ty -> context t TUnit -> expr [] a -> context t a
  | AddLeft: #t:ty -> context t TInt -> expr [] TInt -> context t TInt
  | AddRight: #t:ty -> int -> context t TInt -> context t TInt
  | EqLeft: #t:ty -> context t TInt -> expr [] TInt -> context t TBool
  | EqRight: #t:ty -> int -> context t TInt -> context t TBool
  | AllocCtx: #t:ty -> context t TInt -> context t TRef
  | LoadCtx: #t:ty -> context t TRef -> context t TInt
  | StoreLeft: #t:ty -> context t TRef -> expr [] TInt -> context t TUnit
  | StoreRight: #t:ty -> H.core_ref -> context t TInt -> context t TUnit
  | CasRef: #t:ty -> context t TRef -> expr [] TInt -> expr [] TInt -> context t TBool
  | CasExpected: #t:ty -> H.core_ref -> context t TInt -> expr [] TInt -> context t TBool
  | CasDesired: #t:ty -> H.core_ref -> int -> context t TInt -> context t TBool
  | NodeData: #t:ty -> context t TInt -> expr [] TRef -> context t TRef
  | NodeNext: #t:ty -> int -> context t TRef -> context t TRef
  | ReadDataCtx: #t:ty -> context t TRef -> context t TInt
  | ReadNextCtx: #t:ty -> context t TRef -> context t TRef
  | WriteNextLeft: #t:ty -> context t TRef -> expr [] TRef -> context t TUnit
  | WriteNextRight: #t:ty -> H.core_ref -> context t TRef -> context t TUnit

let rec fill (#a #b:ty) (k:context a b) (e:expr [] a)
  : Tot (expr [] b) (decreases k)
  = match k with
    | Hole -> e
    | LetCtx k body -> Let (fill k e) body
    | IfCtx k e1 e2 -> If (fill k e) e1 e2
    | SeqCtx k e2 -> Seq (fill k e) e2
    | AddLeft k e2 -> Add (fill k e) e2
    | AddRight v k -> Add (Val v) (fill k e)
    | EqLeft k e2 -> Eq (fill k e) e2
    | EqRight v k -> Eq (Val v) (fill k e)
    | AllocCtx k -> Alloc (fill k e)
    | LoadCtx k -> Load (fill k e)
    | StoreLeft k e2 -> Store (fill k e) e2
    | StoreRight r k -> Store (Val r) (fill k e)
    | CasRef k e2 e3 -> Cas (fill k e) e2 e3
    | CasExpected r k e3 -> Cas (Val r) (fill k e) e3
    | CasDesired r v k -> Cas (Val r) (Val v) (fill k e)
    | NodeData k next -> NewNode (fill k e) next
    | NodeNext data k -> NewNode (Val data) (fill k e)
    | ReadDataCtx k -> ReadData (fill k e)
    | ReadNextCtx k -> ReadNext (fill k e)
    | WriteNextLeft k next -> WriteNext (fill k e) next
    | WriteNextRight r k -> WriteNext (Val r) (fill k e)
