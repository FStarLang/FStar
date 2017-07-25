module FStar.Heap

include FStar.Monotonic.Heap

let trivial_preorder (a:Type0) = fun x y -> True

type ref (a:Type0) = mref a (trivial_preorder a)

(*** Untyped views of references *)

(* Definition and ghost decidable equality *)
noeq type aref' :Type0 = {
  a_addr: nat;
  a_mm:   bool;  //manually managed flag
}
let aref = aref'
let dummy_aref = {
  a_addr = 0;
  a_mm   = false;
}
let aref_equal a1 a2 = a1.a_addr = a2.a_addr && a1.a_mm = a2.a_mm

(* Introduction rule *)
let aref_of #t r = {
  a_addr = r.addr;
  a_mm   = r.mm;
}

(* Operators lifted from ref *)
let addr_of_aref a = a.a_addr
let addr_of_aref_of #t r = ()
let aref_is_mm a = a.a_mm
let is_mm_aref_of #t r = ()
let aref_unused_in a h = None? (h.memory a.a_addr)
let unused_in_aref_of #t r h = ()
let contains_aref_unused_in #a h x y = ()

(* Elimination rule *)
let aref_live_at (h: heap) (a: aref) (t: Type0) =
  let maybe_raw_contents = h.memory a.a_addr in
  Some? maybe_raw_contents /\ (
    let raw_contents = Some?.v maybe_raw_contents in (
      dfst raw_contents == t /\ (
        let contents = dsnd raw_contents in
        contents.c_mm == a.a_mm
  )))

let ref_of'
  (h: heap)
  (a: aref)
  (t: Type0)
: Pure (ref t)
  (requires (aref_live_at h a t))
  (ensures (fun _ -> True))
= let raw_contents = Some?.v (h.memory a.a_addr) in
  let contents: ref_contents t = dsnd raw_contents in
  {
    addr = a.a_addr;
    init = contents.c_init;
    mm = contents.c_mm
  }

let gref_of a t =
  let m : squash (exists (h: heap) . aref_live_at h a t) = () in
  let l : (exists (h: heap) . aref_live_at h a t) =
    Squash.join_squash #(h: heap & aref_live_at h a t) m
  in
  let k : (exists (h: heap { aref_live_at h a t} ) . squash True ) =
    FStar.Squash.bind_squash
      #(h: heap & aref_live_at h a t)
      #(h: (h: heap { aref_live_at h a t} ) & squash True)
      l
      (fun h -> let (| h', _ |) = h in Squash.return_squash (| h', () |) )
  in
  let h = FStar.ErasedLogic.exists_proj1 #(h: heap {aref_live_at h a t}) #(fun _ -> squash True) k in
  ref_of' h a t

let ref_of h a t = ref_of' h a t

let aref_live_at_aref_of h #t r = ()
let contains_gref_of h a t = ()
let aref_of_gref_of a t = ()
let gref_of_aref_of #t r = ()

let _eof = ()
