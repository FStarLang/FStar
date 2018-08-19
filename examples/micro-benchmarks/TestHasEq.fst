module TestHasEq

type mlist (a:Type) =
  | MNil : mlist a
  | MCons: hd:a -> tl:nlist a -> mlist a

and nlist (a:Type) =
  | NNil : nlist a
  | NCons: hd:a -> tl:mlist a -> nlist a

let test1 _ = assert (hasEq (mlist nat) /\ hasEq (nlist nat))

//the default, optimized hasEq scheme fails for type t
//as it cannot prove that (b x) has decidable equality
//so either, one can use noeq, in which case F* will not
//allow decidable equality on t
//or, one can say unopteq in which case, F* will use an
//alternate, unoptimized hasEq scheme
//using the alternate scheme, we can, e.g., prove test2
//but cannot prove hasEq (t nat (fun x -> (y:nat{y > x} -> bool)))
unopteq type t (a:Type) (b:a -> Type) =
  | C: x:a -> y:b x -> t a b

let test2 _ = assert (hasEq (t nat (fun x -> y:nat{y > x})))

type t1 (a:Type) =
  | C1: x:a -> y:nat -> z:nat{z = y + 2} -> t1 a

let test3 = assert (hasEq (t1 bool))

let test4 = assert (hasEq (dtuple2 nat (fun x -> y:nat{y > x})))

assume type tp (t:Type0) : Type0

type t2 (t:Type0{tp t}) =
  | Bad: t2 t

(*
 * hasEq (t3 a) depends on hasEq a, so the eqtype annotation fails
 *)
[@expect_failure]
type t3 (a:Type0) :eqtype =
  | C3: x:a -> t3 a

type t4 (a:Type0) :eqtype =  //this succeeds, since independent of a, t4 hasEq
  | C4 : x:nat -> t4 a
