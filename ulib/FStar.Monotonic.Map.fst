(** A library for monotonic references to partial, dependent maps, with a whole-map invariant *)
module FStar.Monotonic.Map
open FStar.Monotonic.RRef
open FStar.HyperHeap

open FStar.HyperStack
open FStar.HyperStack.ST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef

(* Partial, dependent maps *)
type map' (a:Type) (b:a -> Type) =
  f:(x:a -> Tot (option (b x)))

(* Partial, dependent maps, with a whole-map invariant *)
type map (a:Type) (b:a -> Type) (inv:map' a b -> Type0) =
  m:map' a b{inv m}

let upd (#a:eqtype) #b (m:map' a b) (x:a) (y:b x)
  : Tot (map' a b)
  = fun z -> if x = z then Some y else m z

let sel #a #b (m:map' a b) (x:a)
  : Tot (option (b x))
  = m x

abstract let grows #a #b (m1:map' a b) (m2:map' a b) =
  forall x.{:pattern (Some? (m1 x))}
      Some? (m1 x) ==> Some? (m2 x) /\ Some?.v (m1 x) == Some?.v (m2 x)

let grows_reflexive #a #b (m1:map' a b)
  : Lemma (ensures (grows m1 m1))
  = ()

let grows_transitive #a #b (m1:map' a b) (m2:map' a b) (m3:map' a b)
  : Lemma (ensures (grows m1 m2 /\ grows m2 m3 ==> grows m1 m3))
  = ()

let grows_monotone #a #b
  : Lemma (monotonic (map' a b) grows)
  = ()

(* Monotone, partial, dependent maps, with a whole-map invariant *)
type t r a b inv = m_rref r (map a b inv) grows  //maybe grows can include the inv?

let empty_map a b
  : Tot (map' a b)
  = fun x -> None

type rid = MR.rid

let alloc (#r:rid) #a #b #inv
  : ST (t r a b inv)
       (requires (fun h -> inv (empty_map a b)))
       (ensures (fun h0 x h1 ->
    inv (empty_map a b) /\
    ralloc_post r (empty_map a b) h0 (as_hsref x) h1))
  = grows_monotone #a #b;
    FStar.Monotonic.RRef.m_alloc r (empty_map a b)

let defined #r #a #b #inv (m:t r a b inv) (x:a) (h:HS.mem)
  : GTot Type0
  = Some? (sel (m_sel h m) x)

let contains #r #a #b #inv (m:t r a b inv) (x:a) (y:b x) (h:HS.mem)
  : GTot Type0
  = Some? (sel (m_sel h m) x) /\ Some?.v (sel (m_sel h m) x) == y

let value #r #a #b #inv (m:t r a b inv) (x:a) (h:HS.mem{defined m x h})
  : GTot (r:b x{contains m x r h})
  = Some?.v (sel (m_sel h m) x)

let fresh #r #a #b #inv (m:t r a b inv) (x:a) (h:HS.mem)
  : GTot Type0
  = None? (sel (m_sel h m) x)

let map_contains #a #b (m1:map' a b) (m2:map' a b) (x:a) (y:b x)
  : Lemma (requires (grows m1 m2))
    (ensures (Some? (m1 x) /\ m1 x == Some y ==> m2 x == Some y))
  = ()

let contains_stable #r #a #b #inv (m:t r a b inv) (x:a) (y:b x)
  : Lemma (ensures (stable_on_t m (contains m x y)))
  = ()

let extend (#r:rid) (#a:eqtype) (#b:a -> Type) (#inv:(map' a b -> Type0)) (m:t r a b inv) (x:a) (y:b x)
  : ST unit
      (requires (fun h -> let cur = m_sel h m in inv (upd cur x y) /\ sel cur x == None))
      (ensures (fun h0 u h1 ->
      let cur = m_sel h0 m in
      let hsref = as_hsref m in
            m_contains m h1
            /\ modifies (Set.singleton r) h0 h1
            /\ modifies_rref r (Set.singleton (Heap.addr_of (HH.as_ref (HS.MkRef?.ref hsref)))) h0.h h1.h
            /\ m_sel h1 m == upd cur x y
            /\ witnessed (defined m x)
            /\ witnessed (contains m x y)))
  = m_recall m;
    let cur = m_read m in
    m_write m (upd cur x y);
    contains_stable m x y;
    witness m (defined m x);
    witness m (contains m x y)

let lookup #r #a #b #inv (m:t r a b inv) (x:a)
  : ST (option (b x))
       (requires (fun h -> True))
       (ensures (fun h0 y h1 ->
       h0==h1 /\
       y == sel (m_sel h1 m) x /\
       (None? y ==> fresh m x h1) /\
       (Some? y ==>
         defined m x h1 /\
         contains m x (Some?.v y) h1 /\
         witnessed (defined m x) /\
         witnessed (contains m x (Some?.v y)))))
=
  let y = sel (m_read m) x in
  match y with
    | None -> y
    | Some b ->
        contains_stable m x b;
        witness m (defined m x);
        witness m (contains m x b);
        y
