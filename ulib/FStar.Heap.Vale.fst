module FStar.Heap.Vale

open FStar.Seq
open FStar.Heap

type byte
assume HasEq_byte: hasEq byte

type bytes = seq byte

assume val b0:byte
assume val b1:byte
assume val b2:byte

assume Distinct_bytes: b0 <> b1 /\ b1 <> b2 /\ b2 <> b0

let marshal_bool (b:bool) :(b:bytes)  =
  create 1 (if b then b1 else b0)

let unmarshal_bool (b:bytes) :option bool =
  if length b = 1 then
    let b = index b 0 in
    if b = b1 then Some true
    else if b = b0 then Some false
    else None
  else None

type rtti =
  | Bool

let type_of (r:rtti) :Type =
  match r with
  | Bool -> bool

(* let lemma_rtti_injective (r1:rtti) (r2:rtti) *)
(*   :Lemma (requires True) *)
(*          (ensures  (type_of r1 == type_of r2 ==> r1 == r2)) *)
(*          [SMTPat (type_of r1); SMTPat (type_of r2)] *)
(*   = () *)

let size_of (r:rtti) :nat =
  match r with
  | Bool -> 1

let marshal (#r:rtti) (x:type_of r) :(b:bytes{length b = size_of r}) =
  match r with
  | Bool -> marshal_bool x

let unmarshal (r:rtti) (b:bytes) :option (type_of r) =
  match r with
  | Bool -> unmarshal_bool b

let lemma_marshal_unmarshal_inverse (r:rtti) (x:type_of r)
  :Lemma (unmarshal r (marshal x) = Some x)
  = ()

(* addresses in hi-level and lo-level view are nats *)
type hi_addr = nat
type lo_addr = nat

(* low-level view of the memory, map from address to byte *)
private type lo_view = lo_addr -> byte

(*
 * high level view of the memory is just heap
 * Heap.addr_of gives address of a hi-level reference
 *)
private type hi_view = heap

(** start metadata components **)

(*
 * map low-level address a to (rtti, addr), where addr is the address of the high level reference
 * whose low-level view contains a
 *)
private type md_lo_to_hi = lo_addr -> (rtti * hi_addr)

(*
 * map hi-level address a to (lo_start, lo_end), the range of addresses in the lo-level view of a's value
 *)
private type md_hi_to_lo = hi_addr -> (p:(lo_addr * lo_addr){snd p >= fst p})

(*
 * if this hi-level address value is synchronized with its lo-level view
 *)
private type sync_t = hi_addr -> bool

(*
 * metadata maintains mappings from hi-to-lo, lo-to-hi
 * a lo_ctr to keep track of the next lo-level address to use for next alloc
 * and sync to maintain which refs in hi-level are not synchronized with their lo-level view
 *)
private noeq type metadata_t = {
  hi_lo : md_hi_to_lo;
  lo_hi : md_lo_to_hi;
  lo_ctr: nat;
  sync  : sync_t
}

(*
 * mem contains the hi-level heap, lo-level map from addresses to bytes, and the metadata
 *)
abstract noeq type mem = {
  hi:hi_view;
  lo:lo_view;
  md:metadata_t;
}

(*
 * starting at address a0, update the low-level view with bytes b
 *)
private let update_lo_view (r:rtti) (l:lo_view) (a0:lo_addr) (b:bytes{length b = size_of r}) :lo_view =
  match r with
  | Bool ->
    fun a -> if a = a0 then index b 0 else l a

(*
 * update the hi-level view, with the unmarshaling of bytes b
 * unmarshaling either succeeds, in which case the heap is updated and sync map is updated to reflect that the ref is now synced
 * or it fails, in which case the heap is left unchanged and the sync map is updated to reflect that this ref is now not in sync
 *)
private let update_hi_view (r:rtti) (h:heap) (s:sync_t) (h_addr:nat) (b:bytes) :(heap * sync_t) =
  let v_opt = unmarshal r b in
  match v_opt with
  | Some v -> upd_addr #(type_of r) h h_addr v, (fun x -> if x = h_addr then true else s x)  //success
  | None   -> h, (fun x -> if x = h_addr then false else s x)  //failure
    
(*
 * update the lo-to-hi metadata to map addresses starting at a0 to rtti r and hi-level address ha
 * it will map (size_of rtti) addresses starting from a0 in lh
 *)
private let update_md_lo_to_hi (r:rtti) (lh:md_lo_to_hi) (a0:lo_addr) (ha:hi_addr) :md_lo_to_hi =
  match r with
  | Bool ->
    fun a -> if a = a0 then (r, ha) else lh a

(*
 * update hi-to-lo metadata
 *)
private let update_md_hi_to_lo (hl:md_hi_to_lo) (href:hi_addr) (lo_start:lo_addr) (lo_end:lo_addr{lo_end >= lo_start}) :md_hi_to_lo =
  fun r -> if r = href then (lo_start, lo_end) else hl r

let get_lo_start (m:mem) (a:hi_addr) :lo_addr =
  fst (m.md.hi_lo a)

(*
 * alloc function
 * uses Heap.alloc to allocate in the hi-level
 * then allocates addresses in the lo-level view, maps them appropriately, and record the metadata
 *)
abstract let alloc (#r:rtti) (m:mem) (x:type_of r) :GTot (ref (type_of r) * mem) =
  let hi0, lo0, md0 = m.hi, m.lo, m.md in
  let hl0, lh0, c0, s0 = md0.hi_lo, md0.lo_hi, md0.lo_ctr, md0.sync in
  
  let href, hi1 = alloc hi0 x false in  //allocate in the hi-level heap
  let href_addr = addr_of href in

  let lo1 = update_lo_view r lo0 c0 (marshal #r x) in  //update the lo-level view ... note that we start with address c0 -- the value of the counter in metadata of m0

  let lo_start = c0 in
  let lo_end = c0 + (size_of r) - 1 in  //this is the range to which the reference is mapped to

  let hl1 = update_md_hi_to_lo hl0 href_addr lo_start lo_end in  //update the hi-to-lo metadata
  let lh1 = update_md_lo_to_hi r lh0 lo_start href_addr in  //update the lo-to-hi metadata
  let c1 = lo_end + 1 in  //the new counter value for the lo-level view
  let s1 = fun x -> if x = href_addr then true else s0 x in  //the newly allocated ref is synchronized

  (* package up *)
  let md1 = { hi_lo = hl1; lo_hi = lh1; lo_ctr = c1; sync = s1 } in

  href, { hi = hi1; lo = lo1; md = md1 }

(* no allocation in the lo-level directly *)

(*
 * we have two varieties of select and update
 * the code operating on hi-level view uses sel and upd
 * and the code operating on lo-level view uses load and store
 *)

(*
 * sel function -- use Heap.sel
 *)
abstract let sel (#r:rtti) (m:mem) (href:ref (type_of r)) :GTot (type_of r) =
  sel m.hi href

(*
 * upd function
 * use Heap.upd, and sync the lo-level view and update the metadata
 *)
abstract let upd (#r:rtti) (m:mem) (href:ref (type_of r)) (x:type_of r) :GTot mem =
  let hi0, lo0, md0 = m.hi, m.lo, m.md in
  let s0 = md0.sync in
  let href_addr = addr_of href in
  
  let hi1 = upd hi0 href x in  //update in the hi-level heap

  let b = marshal #r x in
  let lo1 = update_lo_view r lo0 (get_lo_start m href_addr)  b in  //update the lo-level view with marshaled bytes, start at (get_lo_start)

  let s1 = fun x -> if x = href_addr then true else s0 x in  //the hi-level ref is now synchronized with the lo-level view

  (* package up *)
  let md1 = { md0 with sync = s1 } in

  { hi = hi1; lo = lo1; md = md1 }

(*
 * this will be implemented
 * read bytes starting from lo_start to lo_end
 *)
assume val read_lo (lo:lo_view) (lo_start:nat) (lo_end:nat{lo_end >= lo_start})
  :(b:bytes{length b = lo_end - lo_start + 1 /\
            (forall (i:nat). (i < length b) ==> index b i = lo (lo_start + i))})

(*
 * lo-level read operation, just return the byte
 *)
abstract let load (m:mem) (a:nat) :byte = m.lo a

(*
 * lo-level store
 * change the lo-level memory, reflect it in the hi-level heap, and update the sync map
 *)
abstract let store (m:mem) (a:nat) (b:byte) :GTot mem =
  let hi0, lo0, md0 = m.hi, m.lo, m.md in

  let hl, lh, s0 = md0.hi_lo, md0.lo_hi, md0.sync in

  let lo1 = fun a' -> if a' = a then b else lo0 a' in  //change the lo-level mapping

  let (r, ref_addr) = lh a in
  let lo_start, lo_end = hl ref_addr in  //use the metadata to get the start and end of lo-level view, rtti r, and ref_addr -- the address of the hi-level reference

  let b = read_lo lo1 lo_start lo_end in  //read bytes [lo_start, lo_end]

  let hi1, s1 = update_hi_view r hi0 s0 ref_addr b in  //update the hi-level view, s1 is the new sync map

  (* package up *)
  let md1 = { md0 with sync = s1 } in

  { m with hi = hi1; lo = lo1; md = md1 }

(* predicate for if the memory is synchronized *)
abstract let sync (m:mem) = forall (a:nat). m.md.sync a == true

let lemma_low_view_is_projection
