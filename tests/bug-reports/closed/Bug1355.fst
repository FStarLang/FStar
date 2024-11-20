module Bug1355

assume val t: v:(int -> Type) -> (i:int -> v i -> Type0) -> Type

irreducible type w #v #r (x:t v r) = True

noeq type u = 
| U:
  k: (i:int -> Type) ->
  x: t k (fun _ _ -> True) ->
  f: (i:int -> Tot (y:k i{w x})) ->
  u

module B   = LowStar.Buffer

assume val struct (a:Type0) :Type0

noeq type t2 =
  | C2: x:int -> fld:B.pointer (struct (u:int{u < x})) -> t2


noeq type t3 = | T3 :
  (u: (nat -> Type0)) ->
  (f: ((x: nat & u x) -> Type0)) ->
  (x: nat) -> (y: u x) -> (z: f (| x, y |)) -> t3


noeq type g
  (u: (nat -> Type0))
  (f: ((x: nat & u x) -> Type0))
  (x: nat)
  (y: u x)
= | G : (r: (f (| x, y |))) -> g u f x y

noeq
type monad (m:Type0 -> Type0) : Type = {
  bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
  assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
			 squash (bind (bind x f) g == bind x (fun y -> bind (f y) g));
}

open FStar.Ghost

noeq type t5 = {
  x: erased int;
  y: erased (y:int{y>= reveal x});
  y_: (y_:int{y_ = reveal y});
}

noeq
type monad2 (rr : Type) (m:Type0 -> Type0) : Type = {
  ret    : #a:_ -> a -> m a;
  bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
  assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
			 squash (bind (bind x f) g == bind x (fun y -> bind (f y) g));
  id1    : #a:_ -> #b:_ -> x:a -> f:(a -> m b) ->
           squash (bind (ret x) f == f x);
  id2    : #a:_ -> c:m a ->
           squash (bind c ret == c);
}


let rec for_all_range (n: nat) (f: (i: nat{i < n}) -> bool) =
  if n = 0 then
    true
  else (
    f (n - 1) && for_all_range (n - 1) f
  )

noeq
type test_t =
  | MkTestT:
    s: list nat ->
    lem: squash (for_all_range (List.Tot.length s) (fun (i: nat{i < List.Tot.length s}) -> true)) ->
    test_t

noeq type t6 = | T :
  (u: (nat -> Type0)) ->
  (f: ((x: nat & u x) -> Type0)) ->
  (x: nat) -> (y: u x) -> (z: g u f x y) -> t6

noeq type g2
  (u: (nat -> Type0))
  (f: ((x: nat & u x) -> Type0))
  (x: nat)
  (y: u x)
= | G2 : (r: (f (| x, y |))) -> g2 u f x y


(*
 * Examples from #1276
 *)

assume val type_mapper: n:nat -> Type0

noeq
type container =
  | TC:
    pred:(n:nat -> Type0) ->
    n:(let t i = pred i in k:nat{type_mapper k == i:nat{t i}}) ->
    container


noeq type type_container0 =
  | TC0:
    t: Type0 ->
    type_container0

let create() =
  let tc = TC0 int in
  let t1 = tc.t in
  let t2 = int in
  assert(t1 == t2);
  assert(i1:(t1){True} == i2:(t2){True})
