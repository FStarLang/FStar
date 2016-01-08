module PureMonad

open FunctionalExtensionality

(* Monad laws *)

(* Problem: can't write type equality as ==, but can use EqTyp *)

val eqTyp_trans : a:Type -> b:Type -> c:Type ->
  Lemma (requires (EqTyp a b /\ EqTyp b c)) (ensures (EqTyp a c))
let eqTyp_trans (a:Type) (b:Type) (c:Type) = ()

(* Without kind polymorphism can only express equality at kind Type *)

(* In particular can't express extensional equivalence of predicates *)

(* kind TPred (a:Type) = a -> Type *)

(* opaque logic type FTEq (a:Type) (f:TPred a) (g:TPred a) = *)
(*   (forall x. EqTyp (f x) (g x)) -- a should be a kind not a type here *)

val left_identity : a:Type -> b:Type -> x:a -> f:(a -> PureWP b) ->
  p:(b->Type) -> Lemma (EqTyp (pure_bind_wlp a b (pure_return a x) f p) (f x p))
let left_identity (a:Type) (b:Type) (x:a) (f:(a -> PureWP b)) (p:(b->Type)) = ()

val right_identity : a:Type -> m:(PureWP a) ->
  p:(a->Type) -> Lemma (EqTyp (pure_bind_wlp a a m (pure_return a) p) (m p))
let right_identity (a:Type) (m:(PureWP a)) (p:(a->Type)) = ()
(*
../../bin/fstar.exe ../../lib/FStar.FunctionalExtensionality.fst pure.fst
pure.fst(28,0-28,61): Unknown assertion failed
Error: 1 errors were reported (see above)
 *)

(*
assume val associativity : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (pure_bind_wlp b c (pure_bind_wlp a b m f) g p)
                      (pure_bind_wlp a c m (fun x -> pure_bind_wlp b c (f x) g) p)
(* let associativity (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b)) *)
(*   (g:(b -> PureWP c)) (p:(c->Type)) = TEq *)
(*
pure.fst(37,38-38,0): Subtyping check failed; expected type
(EqTyp (pure_bind_wlp b c (pure_bind_wlp a b m f) g p)
      (pure_bind_wlp a c m (fun x -> (pure_bind_wlp b c (f x) g)) p)); got type
(EqTyp (pure_bind_wlp b c (pure_bind_wlp a b m f) g p)
      (pure_bind_wlp b c (pure_bind_wlp a b m f) g p))

(pure_bind_wlp b c (pure_bind_wlp a b m f) g p) =
(pure_bind_wlp b c (fun p -> m (fun y -> f y p)) g p) =
(fun p -> m (fun x -> f x p)) (fun y -> g y p) =
m (fun x -> f x (fun y -> g y p))

(pure_bind_wlp a c m (fun x -> (pure_bind_wlp b c (f x) g)) p)) =
m (fun y -> (fun x -> (pure_bind_wlp b c (f x) g)) y p) = (reduction under binders!)
m (fun y -> (pure_bind_wlp b c (f y) g) p) = (reduction under binders!)
m (fun y -> f y (fun z -> g z p))
 *)

(* Checking whether reduction under binders is the problem: *)
val test : a:Type -> f:((a -> Type) -> Type) ->
  EqTyp (f (fun (x:a) -> (fun (y:Type) -> y) int))
       (f (fun (x:a) -> int))
let test (a:Type) (f:((a -> Type) -> Type)) = TEq
(* Surprisingly, it works! *)

(* Also the two tricky reduction steps work in isolation *)
val test1 : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (m (fun y -> (fun x -> (pure_bind_wlp b c (f x) g)) y p))
                      (m (fun y -> (pure_bind_wlp b c (f y) g) p))
let test1 (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
      (g:(b -> PureWP c)) (p:(c->Type)) = TEq

val test2 : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (m (fun y -> (pure_bind_wlp b c (f y) g) p))
                      (m (fun y -> f y (fun z -> g z p)))
let test2 (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
      (g:(b -> PureWP c)) (p:(c->Type)) = TEq

val test12 : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (m (fun y -> (fun x -> (pure_bind_wlp b c (f x) g)) y p))
                      (m (fun y -> f y (fun z -> g z p)))
let test12 (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
      (g:(b -> PureWP c)) (p:(c->Type)) = TEq

val test012 : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (m (fun y -> f y (fun z -> g z p)))
                      ((pure_bind_wlp a c m
                         (fun x -> (pure_bind_wlp b c (f x) g)) p))

let test012 (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
      (g:(b -> PureWP c)) (p:(c->Type)) = TEq

val test012' : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (pure_bind_wlp b c (pure_bind_wlp a b m f) g p)
                      (m (fun x -> f x (fun y -> g y p)))
let test012' (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
      (g:(b -> PureWP c)) (p:(c->Type)) = TEq

val alpha : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (m (fun x -> f x (fun y -> g y p)))
                      (m (fun y -> f y (fun z -> g z p)))
let alpha (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
      (g:(b -> PureWP c)) (p:(c->Type)) = TEq

(* But we still can only put it all together manually with transitivity *)
val associativity' : a:Type -> b:Type -> c:Type ->
                    m:(PureWP a) -> f:(a -> PureWP b) -> g:(b -> PureWP c) ->
  p:(c->Type) -> EqTyp (pure_bind_wlp b c (pure_bind_wlp a b m f) g p)
                      (pure_bind_wlp a c m (fun x -> pure_bind_wlp b c (f x) g) p)
let associativity' (a:Type) (b:Type) (c:Type) (m:(PureWP a)) (f:(a -> PureWP b))
    (g:(b -> PureWP c)) (p:(c->Type)) =
  EqTyp_trans (test012' a b c m f g p) (test012 a b c m f g p)
 *)
