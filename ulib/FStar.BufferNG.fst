// with: --include ulib --include ulib/hyperstack

module FStar.BufferNG
module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = FStar.Pointer
open HST

(* Buffers *)

noeq private type buffer_root (t: Type) =
| BufferRootSingleton:
  (p: P.pointer t) ->
  buffer_root t
| BufferRootArray:
  (#max_length: UInt32.t) ->
  (p: P.pointer (P.array max_length t)) ->
  buffer_root t

private let buffer_root_length (#t: Type) (b: buffer_root t): Tot UInt32.t = match b with
| BufferRootSingleton _ -> 1ul
| BufferRootArray #t #len _ -> len

noeq private type _buffer (t: Type) =
| Buffer:
  (broot: buffer_root t) ->
  (bidx: UInt32.t) ->
  (blength: UInt32.t { UInt32.v bidx + UInt32.v blength <= UInt32.v (buffer_root_length broot) } ) ->
  _buffer t
abstract let buffer (t: Type): Tot Type = _buffer t

abstract let gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: GTot (buffer t)
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Stack (buffer t)
  (requires (fun h -> P.live h p))
  (ensures (fun h b h' -> h' == h /\ b == gsingleton_buffer_of_pointer p))
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: GTot (buffer t)
= Buffer (BufferRootArray p) 0ul length

abstract let buffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Stack (buffer t)
  (requires (fun h -> P.live h p))
  (ensures (fun h b h' -> h' == h /\ b == gbuffer_of_array_pointer p))
= Buffer (BufferRootArray p) 0ul length

abstract let length
  (#t: Type)
  (b: buffer t)
: GTot UInt32.t
= Buffer?.blength b

abstract let length_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (length (gsingleton_buffer_of_pointer p) == 1ul))
  [SMTPat (length (gsingleton_buffer_of_pointer p))]
= ()

abstract let length_gbuffer_of_array_pointer
  (#t: Type)
  (#len: UInt32.t)
  (p: P.pointer (P.array len t))
: Lemma
  (requires True)
  (ensures (length (gbuffer_of_array_pointer p) == len))
  [SMTPat (length (gbuffer_of_array_pointer p))]
= ()

abstract let live
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= UInt32.v (length b) > 0 /\ ( // needed to preserve liveness through modifies
    match b.broot with
    | BufferRootSingleton p -> P.live h p
    | BufferRootArray #mlen p -> P.live h p
  )

abstract let live_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
  (h: HS.mem)
: Lemma
  (ensures (live h (gsingleton_buffer_of_pointer p) <==> P.live h p ))
  [SMTPat (live h (gsingleton_buffer_of_pointer p))]
= ()

abstract let live_gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
  (h: HS.mem)
: Lemma
  (requires (UInt32.v length > 0))
  (ensures (live h (gbuffer_of_array_pointer p) <==> P.live h p))
  [SMTPat (live h (gbuffer_of_array_pointer p))]
= ()

abstract let frameOf
  (#t: Type)
  (b: buffer t)
: GTot HH.rid
= match b.broot with
  | BufferRootSingleton p -> P.frameOf p
  | BufferRootArray #mlen p -> P.frameOf p

abstract let frameOf_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (ensures (frameOf (gsingleton_buffer_of_pointer p) == P.frameOf p))
  [SMTPat (frameOf (gsingleton_buffer_of_pointer p))]
= ()

abstract let frameOf_gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Lemma
  (ensures (frameOf (gbuffer_of_array_pointer p) == P.frameOf p))
  [SMTPat (frameOf (gbuffer_of_array_pointer p))]
= ()

abstract let gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: GTot (buffer t)
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let sub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Stack (buffer t)
  (requires (fun h -> live h b))
  (ensures (fun h b' h' -> h' == h /\ b' == gsub b i len ))
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let length_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (length (gsub b i len) == len))
  [SMTPat (length (gsub b i len))]
= ()

abstract let live_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
  (h: HS.mem)
: Lemma
  (requires (UInt32.v len > 0))
  (ensures (live h (gsub b i len) <==> live h b))
  [SMTPat (live h (gsub b i len))]
= ()

abstract let gsub_gsub
  (#a: Type)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t{UInt32.v i1 + UInt32.v len1 <= UInt32.v (length b)})
  (i2: UInt32.t)
  (len2: UInt32.t {UInt32.v i2 + UInt32.v len2 <= UInt32.v len1})
: Lemma
  (ensures (gsub (gsub b i1 len1) i2 len2 == gsub b FStar.UInt32.(i1 +^ i2) len2))
= ()

abstract let gsub_zero_length
  (#a: Type)
  (b: buffer a)
: Lemma
  (ensures (gsub b 0ul (length b) == b))
= ()

private let buffer_root_as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer_root t)
: GTot (Seq.seq t)
= match b with
  | BufferRootSingleton p ->
    Seq.create 1 (P.gread h p)
  | BufferRootArray p ->
    P.gread h p

private let length_buffer_root_as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer_root t)
: Lemma
  (requires True)
  (ensures (Seq.length (buffer_root_as_seq h b) == UInt32.v (buffer_root_length b)))
  [SMTPat (Seq.length (buffer_root_as_seq h b))]
= ()

abstract let as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: GTot (Seq.seq t)
= let i = UInt32.v (Buffer?.bidx b) in
  Seq.slice (buffer_root_as_seq h (Buffer?.broot b)) i (i + UInt32.v (Buffer?.blength b))

abstract let length_as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires True)
  (ensures (Seq.length (as_seq h b) == UInt32.v (length b)))
  [SMTPat (Seq.length (as_seq h b))]
= ()

abstract let as_seq_gsingleton_buffer_of_pointer
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (as_seq h (gsingleton_buffer_of_pointer p) == Seq.create 1 (P.gread h p)))
  [SMTPat (as_seq h (gsingleton_buffer_of_pointer p))]
= Seq.slice_length (Seq.create 1 (P.gread h p))

abstract let as_seq_gbuffer_of_array_pointer
  (#length: UInt32.t)
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer (P.array length t))
: Lemma
  (requires True)
  (ensures (as_seq h (gbuffer_of_array_pointer p) == P.gread h p))
  [SMTPat (as_seq h (gbuffer_of_array_pointer p))]
= Seq.slice_length (P.gread h p)

abstract let as_seq_gsub
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (as_seq h (gsub b i len) == Seq.slice (as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len)))
  [SMTPat (as_seq h (gsub b i len))]
= Seq.slice_slice (buffer_root_as_seq h (Buffer?.broot b)) (UInt32.v (Buffer?.bidx b)) (UInt32.v (Buffer?.bidx b) + UInt32.v (Buffer?.blength b)) (UInt32.v i) (UInt32.v i + UInt32.v len)

abstract let gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: GTot (P.pointer t)
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    P.gcell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let pointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: Stack (P.pointer t)
  (requires (fun h -> live h b))
  (ensures (fun h p h' -> h' == h /\ p == gpointer_of_buffer_cell b i))
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    P.cell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let gpointer_of_buffer_cell_gsub
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len: UInt32.t { UInt32.v i1 + UInt32.v len <= UInt32.v (length b) } )
  (i2: UInt32.t { UInt32.v i2 < UInt32.v len } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gsub b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)))
  [SMTPat (gpointer_of_buffer_cell (gsub b i1 len) i2)]
= ()

abstract let live_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
  (h: HS.mem)
: Lemma
  (ensures (P.live h (gpointer_of_buffer_cell b i) <==> live h b))
  [SMTPat (P.live h (gpointer_of_buffer_cell b i))]
= ()

abstract let gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
  (i: UInt32.t { UInt32.v i < 1 } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i == p))
  [SMTPat (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i)]
= ()

abstract let gpointer_of_buffer_cell_gbuffer_of_array_pointer
  (#length: UInt32.t)
  (#t: Type)
  (p: P.pointer (P.array length t))
  (i: UInt32.t { UInt32.v i < UInt32.v length } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i == P.gcell p i))
  [SMTPat (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i)]
= ()

abstract let gread_gpointer_of_buffer_cell
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (ensures (P.gread h (gpointer_of_buffer_cell b i) == Seq.index (as_seq h b) (UInt32.v i)))
  [SMTPat (P.gread h (gpointer_of_buffer_cell b i))]
= ()

abstract let gread_gpointer_of_buffer_cell'
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (ensures (P.gread h (gpointer_of_buffer_cell b i) == Seq.index (as_seq h b) (UInt32.v i)))
= ()

abstract let gread_pointer_of_buffer_cell'
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (Seq.index (as_seq h b) (UInt32.v i) == P.gread h (gpointer_of_buffer_cell b i)))
  [SMTPat (Seq.index (as_seq h b) (UInt32.v i))]
= ()

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)

let read
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: HST.Stack t
  (requires (fun h -> live h b))
  (ensures (fun h v h' -> h' == h /\ v == Seq.index (as_seq h b) (UInt32.v i)))
= P.read (pointer_of_buffer_cell b i)

(* buffer write: needs clearer "modifies" clauses *)

abstract let disjoint_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t { UInt32.v i1 < UInt32.v (length b) } )
  (i2: UInt32.t { UInt32.v i2 < UInt32.v (length b) } )
: Lemma
  (requires ( UInt32.v i1 <> UInt32.v i2 ) )
  (ensures (P.disjoint (gpointer_of_buffer_cell b i1) (gpointer_of_buffer_cell b i2)))
  [SMTPat (P.disjoint (gpointer_of_buffer_cell b i1) (gpointer_of_buffer_cell b i2))]
= ()

(* For a "disjoint" clause on buffers, we could use the following TRANSPARENT definitions: *)

unfold
let disjoint_buffer_vs_pointer
  (#t1 #t2: Type)
  (b: buffer t1)
  (p: P.pointer t2)
: GTot Type0
= forall (i: UInt32.t { UInt32.v i < UInt32.v (length b) } ) . P.disjoint (gpointer_of_buffer_cell b i) p

unfold
let disjoint_buffer_vs_buffer
  (#t1 #t2: Type)
  (b1: buffer t1)
  (b2: buffer t2)
: GTot Type0
= forall
    (i1: UInt32.t { UInt32.v i1 < UInt32.v (length b1) } )
    (i2: UInt32.t { UInt32.v i2 < UInt32.v (length b2) } )
  . 
    P.disjoint (gpointer_of_buffer_cell b1 i1) (gpointer_of_buffer_cell b2 i2) 

let write
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
  (v: t)
: HST.Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h _ h' -> 
    P.modifies_1 (gpointer_of_buffer_cell b i) h h' /\
    live h' b /\
    Seq.index (as_seq h' b) (UInt32.v i) == v /\ (
      forall (j: UInt32.t {UInt32.v j < UInt32.v (length b) /\ UInt32.v j <> UInt32.v i }) .
        Seq.index (as_seq h' b) (UInt32.v j) == Seq.index (as_seq h b) (UInt32.v j)    
  )))
= P.write (pointer_of_buffer_cell b i) v

let modifies_1_disjoint_buffer_vs_pointer_live
  (#t1 t2: Type)
  (b: buffer t1)
  (p: P.pointer t2)
  (h h': HS.mem)
: Lemma
  (requires (
    disjoint_buffer_vs_pointer b p /\
    live h b /\
    P.modifies_1 p h h'
  ))
  (ensures (live h' b /\ as_seq h b == as_seq h' b))
= P.modifies_1_reveal p h h';
  let f
    (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
  : Lemma
    (P.live h' (gpointer_of_buffer_cell b i) /\ P.gread h (gpointer_of_buffer_cell b i) == P.gread h' (gpointer_of_buffer_cell b i))
  = if frameOf b = P.frameOf p
    then
      let s = P.set_singleton p in
      let (ap: P.apointer { P.set_amem ap s } ) = P.APointer t2 p in
      P.modifies_elim (P.frameOf p) s h h' (gpointer_of_buffer_cell b i)
    else
      P.modifies_one_other_region (P.frameOf p) h h' (gpointer_of_buffer_cell b i)
  in
  f 0ul; // for the liveness of the whole buffer
  length_as_seq h b;
  length_as_seq h' b;
  let g
    (i: nat { i < UInt32.v (length b) } )
  : Lemma
    (Seq.index (as_seq h b) i == Seq.index (as_seq h' b) i)
  = let j = UInt32.uint_to_t i in
    f j;
    gread_gpointer_of_buffer_cell' h b j;
    gread_gpointer_of_buffer_cell' h' b j
  in
  Classical.forall_intro g;
  Seq.lemma_eq_elim (as_seq h b) (as_seq h' b)
