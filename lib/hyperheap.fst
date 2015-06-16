(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    other-files:set.fsi heap.fst map.fsi
 --*)

module HyperHeap
open Map
open Heap
type rid = int  //region id
type t = Map.t rid heap

new_effect STATE = STATE_h t

private type rref (id:rid) (a:Type) = Prims.ref a
val as_ref : #a:Type -> #id:rid -> r:rref id a -> Tot (ref a)
let as_ref id r = r

private val ref_as_rref : #a:Type -> i:rid -> r:ref a -> Tot (rref i a)
let ref_as_rref i r = r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj i r = ()


effect ST (a:Type) (pre:t -> Type) (post:t -> a -> t -> Type) =
       STATE a (fun 'p m0 -> pre m0 /\ (forall x m1. post m0 x m1 ==> 'p x m1))
               (fun 'p m0 ->  (forall x m1. pre m0 /\ post m0 x m1 ==> 'p x m1))

assume val new_region: unit -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (id:rid) (m1:t) -> exists (h:heap). not(Map.contains m0 id) /\ m1=Map.upd m0 id h))

type Let (#a:Type) (x:a) (body:(a -> Type)) = body x

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) = Heap.sel (Map.sel m i) (as_ref r)
let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)

assume val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> Map.contains m i))
    (ensures (fun m0 x m1 ->
                    Let (Map.sel m0 i) (fun region_i ->
                    not (Heap.contains region_i (as_ref x))
                    /\ m1=Map.upd m0 i (Heap.upd region_i (as_ref x) init))))

assume val op_ColonEquals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _u m1 -> m1= Map.upd m0 i (Heap.upd (Map.sel m0 i) (as_ref r) v)))

assume val op_Bang:#a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m1=m0 /\ x=Heap.sel (Map.sel m0 i) (as_ref r)))

assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

type modifies (s:Set.set rid) (m0:t) (m1:t) =
    Map.Equal m1 (Map.concat m1 (Map.restrict (Set.complement s) m0))

type fresh_region (i:rid) (m0:t) (m1:t) =
  not (Map.contains m0 i)
  /\ Map.contains m1 i

type contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    Map.contains m i /\ Heap.contains (Map.sel m i) (as_ref r)

type fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (Heap.contains (Map.sel m0 i) (as_ref r))
  /\  (Heap.contains (Map.sel m1 i) (as_ref r))

kind STPost (a:Type) = a -> t -> Type
kind STWP (a:Type) = STPost a -> t -> Type

sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:PureWP a) (p:STPost a) (h:t) -> wp (fun a -> p a h)
