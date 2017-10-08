module InitFreezeRef

open FStar.Preorder
open FStar.Heap
open FStar.ST

private type rstate (a:Type) =
  | Empty  : rstate a
  | Mutable: v:a -> rstate a
  | Frozen : v:a -> rstate a

private let evolve_broken0 (a:Type) :relation (rstate a) =
  fun r1 r2 ->
  match r1, r2 with
  | Empty,      Mutable _
  | Mutable _,  Mutable _ -> True
  | Mutable v1, Frozen v2 -> v1 == v2
  | _, _ -> False

(* private let evolve_broken (a:Type) :preorder (rstate a) = evolve_broken0 a
   -- fails as it should *)

private let evolve0 (a:Type) :relation (rstate a) =
  fun r1 r2 ->
  match r1, r2 with
  | Empty,     _
  | Mutable _, Mutable _
  | Mutable _, Frozen _  -> True 
  | Frozen v1, Frozen v2 -> v1 == v2
  | _, _ -> False

private let evolve (a:Type) :preorder (rstate a) = evolve0 a

abstract type eref (a:Type) :Type0 = mref (rstate a) (evolve a)

abstract let addr_of (#a:Type0) (r:eref a) :GTot nat = addr_of r

private let readable_pred (#a:Type0) (r:eref a) :heap_predicate
  = fun h -> h `contains` r /\ (~ (Empty? (sel h r)))

abstract let readable (#a:Type0) (r:eref a) :Type0
  = witnessed (readable_pred r)

private let writable_pred (#a:Type0) (r:eref a) :heap_predicate
  = fun h -> h `contains` r /\ (let x = sel h r in Empty? x \/ Mutable? x)

(* abstract let writable (#a:Type0) (r:eref a) :Type0 = witnessed (writable_pred r)
   -- fails as it should, why? *)

abstract let writable_in (#a:Type0) (r:eref a) (h:heap) :Type0
  = h `contains` r /\ (let x = sel h r in Empty? x \/ Mutable? x)

private let frozen_at_pred (#a:Type0) (r:eref a) (x:a) :heap_predicate
  = fun h -> h `contains` r /\ sel h r == Frozen x

abstract let frozen_at (#a:Type0) (r:eref a) (x:a) :Type0
  = witnessed (frozen_at_pred r x)

abstract let sel (#a:Type0) (h:heap) (r:eref a) :GTot (option a)
  = let x = sel h r in
    match x with
    | Empty     -> None
    | Mutable x
    | Frozen  x -> Some x

abstract let alloc (a:Type0)
  :ST (eref a) (requires (fun _       -> True))
               (ensures  (fun h0 r h1 -> modifies !{} h0 h1 /\ r `writable_in` h1 /\ sel h1 r == None))
  = ST.alloc #(rstate a) #(evolve a) Empty

abstract let read (#a:Type0) (r:eref a{readable r})
  :ST a (requires (fun _       -> True))
        (ensures  (fun h0 x h1 -> h0 == h1 /\ sel h1 r == Some x))
  = ST.gst_recall (readable_pred r);
    let x = ST.read r in
    match x with
    | Mutable x
    | Frozen  x -> x

abstract let write (#a:Type0) (r:eref a) (x:a)
  :ST unit (fun h0      -> r `writable_in` h0)
           (fun h0 _ h1 -> modifies (Set.singleton (addr_of r)) h0 h1 /\
	                readable r                                 /\
	                r `writable_in` h1                         /\
			sel h1 r == Some x)
  = ST.write r (Mutable x);
    gst_witness (readable_pred r)

abstract let freeze (#a:Type0) (r:eref a{readable r})
  :ST a (fun _       -> True)
        (fun h0 x h1 -> modifies (Set.singleton (addr_of r)) h0 h1 /\
	             sel h0 r == sel h1 r                       /\
		     sel h0 r == Some x                         /\
	             r `frozen_at` x)
  = ST.recall r;
    ST.gst_recall (readable_pred r);
    let x = ST.read r in
    let v, y =
      match x with
      | Mutable x
      | Frozen  x -> x, Frozen x
    in
    ST.write r y;
    gst_witness (frozen_at_pred r v);
    v

abstract let recall_freeze (#a:Type0) (r:eref a) (x:a{r `frozen_at` x})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ sel h1 r == Some x))
  = gst_recall (frozen_at_pred r x)

// let alloc (a:Type) = alloc #_ #(evolve a) Empty
// let read (#a:Type) (r:eref a) = match (!r) with | Mutable v | Frozen v -> v
// private let write (#a:Type) (r:eref a) (v:a) = r := Mutable v
// private let freeze (#a:Type) (r:eref a) = r := Frozen (Mutable?.v !r)
// (* TODO: for some reason needed to mark these as private, otherwise
// ./InitFreezeMST.fst(35,41-35,43): (Error) Interface of InitFreezeMST violates its abstraction (add a 'private' qualifier to 'write'?): Too many arguments to function of type a:Type0 -> Prims.Tot (Preorder.preorder (InitFreezeMST.rstate a)); got 3 arguments (see also ./STx.fst(95,25-95,34)) *)

// assume val complex_procedure (r:eref int) : St unit

// let main() : St unit =
//   let r = alloc int in
//   (* ignore (read r) -- fails like it should *)
//   write r 42;
//   ignore (read r);
//   write r 0;
//   witness_token r (fun rs -> ~(Empty? rs));
//   freeze r;
//   (* write r 7; -- fails like it should *)
//   ignore (read r);
//   witness_token r (fun rs -> rs == Frozen 0);
//   complex_procedure r;
//   (* ignore (read r); -- fails like it should *)
//   recall_token r (fun rs -> ~(Empty? rs));
//   let x = read r in
//   (* assert (x == 0) -- fails like it should *)
//   recall_token r (fun rs -> rs == Frozen 0);
//   assert (x == 0)
