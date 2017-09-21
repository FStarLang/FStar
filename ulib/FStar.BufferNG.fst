// with: --include ulib --include ulib/hyperstack

module FStar.BufferNG
module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = FStar.Pointer
open FStar.Pointer
open HST

(* Buffers *)

let buffer (t: typ): Tot Type0 = P.buffer t

let gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: GTot (buffer t)
= P.gsingleton_buffer_of_pointer p

let singleton_buffer_of_pointer
  (#t: typ)
  (p: P.pointer t)
: Stack (buffer t)
  (requires (fun h -> P.live h p))
  (ensures (fun h b h' -> h' == h /\ b == gsingleton_buffer_of_pointer p))
= P.singleton_buffer_of_pointer p

let gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: P.pointer (TArray length t))
: GTot (buffer t)
= P.gbuffer_of_array_pointer p

let buffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: P.pointer (TArray length t))
: Stack (buffer t)
  (requires (fun h -> P.live h p))
  (ensures (fun h b h' -> h' == h /\ b == gbuffer_of_array_pointer p))
= P.buffer_of_array_pointer p

let length
  (#t: typ)
  (b: buffer t)
: GTot UInt32.t
= P.buffer_length b

let length_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (length (gsingleton_buffer_of_pointer p) == 1ul))
  [SMTPat (length (gsingleton_buffer_of_pointer p))]
= ()

let length_gbuffer_of_array_pointer
  (#t: typ)
  (#len: array_length_t)
  (p: P.pointer (TArray len t))
: Lemma
  (requires True)
  (ensures (length (gbuffer_of_array_pointer p) == len))
  [SMTPat (length (gbuffer_of_array_pointer p))]
= ()

let live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= P.buffer_live h b

let live_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: P.pointer t)
  (h: HS.mem)
: Lemma
  (ensures (live h (gsingleton_buffer_of_pointer p) <==> P.live h p ))
  [SMTPat (live h (gsingleton_buffer_of_pointer p))]
= ()

let live_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: P.pointer (TArray length t))
  (h: HS.mem)
: Lemma
  (requires (UInt32.v length > 0))
  (ensures (live h (gbuffer_of_array_pointer p) <==> P.live h p))
  [SMTPat (live h (gbuffer_of_array_pointer p))]
= ()

let frameOf
  (#t: typ)
  (b: buffer t)
: GTot HH.rid
= P.frameOf_buffer b

let frameOf_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: P.pointer t)
: Lemma
  (ensures (frameOf (gsingleton_buffer_of_pointer p) == P.frameOf p))
  [SMTPat (frameOf (gsingleton_buffer_of_pointer p))]
= ()

let frameOf_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: P.pointer (TArray length t))
: Lemma
  (ensures (frameOf (gbuffer_of_array_pointer p) == P.frameOf p))
  [SMTPat (frameOf (gbuffer_of_array_pointer p))]
= ()

let gsub
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Ghost (buffer t)
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (length b)))
  (ensures (fun _ -> True))
= P.gsub_buffer b i len

let sub
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Stack (buffer t)
  (requires (fun h -> UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ live h b))
  (ensures (fun h b' h' -> UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ h' == h /\ b' == gsub b i len ))
= P.sub_buffer b i len

let length_gsub
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ length (gsub b i len) == len))
  [SMTPat (length (gsub b i len))]
= ()

let live_gsub_equiv
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ (live h (gsub b i len) <==> live h b)))
  [SMTPat (live h (gsub b i len))]
= ()

let live_gsub_intro
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ live h b))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ live h (gsub b i len)))
  [SMTPat (live h (gsub b i len))]
= ()

let gsub_gsub
  (#a: typ)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (length b) /\  
    UInt32.v i2 + UInt32.v len2 <= UInt32.v len1
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (length b) /\  
    UInt32.v i2 + UInt32.v len2 <= UInt32.v len1 /\
    gsub (gsub b i1 len1) i2 len2 == gsub b FStar.UInt32.(i1 +^ i2) len2
  ))
  [SMTPat (gsub (gsub b i1 len1) i2 len2)]
= ()

let gsub_zero_length
  (#a: typ)
  (b: buffer a)
: Lemma
  (ensures (gsub b 0ul (length b) == b))
= ()

let as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot (Seq.seq (type_of_typ t))
= P.buffer_as_seq h b

let length_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires True)
  (ensures (Seq.length (as_seq h b) == UInt32.v (length b)))
  [SMTPat (Seq.length (as_seq h b))]
= ()

let as_seq_gsingleton_buffer_of_pointer
  (#t: typ)
  (h: HS.mem)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (as_seq h (gsingleton_buffer_of_pointer p) == Seq.create 1 (P.gread h p)))
  [SMTPat (as_seq h (gsingleton_buffer_of_pointer p))]
= ()

let as_seq_gbuffer_of_array_pointer
  (#length: array_length_t)
  (#t: typ)
  (h: HS.mem)
  (p: P.pointer (TArray length t))
: Lemma
  (requires True)
  (ensures (as_seq h (gbuffer_of_array_pointer p) == P.gread h p))
  [SMTPat (as_seq h (gbuffer_of_array_pointer p))]
= ()

let as_seq_gsub
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ as_seq h (gsub b i len) == Seq.slice (as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len)))
  [SMTPat (as_seq h (gsub b i len))]
= ()

let gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Ghost (P.pointer t)
  (requires (UInt32.v i < UInt32.v (length b)))
  (ensures (fun _ -> True))
= P.gpointer_of_buffer_cell b i

let pointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Stack (P.pointer t)
  (requires (fun h -> UInt32.v i < UInt32.v (length b) /\ live h b))
  (ensures (fun h p h' -> UInt32.v i < UInt32.v (length b) /\ h' == h /\ p == gpointer_of_buffer_cell b i))
= P.pointer_of_buffer_cell b i

let gpointer_of_buffer_cell_gsub
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (len: UInt32.t )
  (i2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len <= UInt32.v (length b) /\
    UInt32.v i2 < UInt32.v len
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len <= UInt32.v (length b) /\
    UInt32.v i2 < UInt32.v len /\
    gpointer_of_buffer_cell (gsub b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)
  ))
  [SMTPat (gpointer_of_buffer_cell (gsub b i1 len) i2)]
= Pointer.gpointer_of_buffer_cell_gsub_buffer b i1 len i2

let live_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (UInt32.v i < UInt32.v (length b)))
  (ensures (UInt32.v i < UInt32.v (length b) /\ P.live h (gpointer_of_buffer_cell b i) <==> live h b))
  [SMTPat (P.live h (gpointer_of_buffer_cell b i))]
= ()

let gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: P.pointer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < 1))
  (ensures (UInt32.v i < 1 /\ gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i == p))
  [SMTPat (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i)]
= ()

let gpointer_of_buffer_cell_gbuffer_of_array_pointer
  (#length: array_length_t)
  (#t: typ)
  (p: P.pointer (TArray length t))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i == P.gcell p i))
  [SMTPat (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i)]
= ()

let gread_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (length b)))
  (ensures (UInt32.v i < UInt32.v (length b) /\ P.gread h (gpointer_of_buffer_cell b i) == Seq.index (as_seq h b) (UInt32.v i)))
  [SMTPat (P.gread h (gpointer_of_buffer_cell b i))]
= ()

let gread_gpointer_of_buffer_cell'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (length b)))
  (ensures (UInt32.v i < UInt32.v (length b) /\ P.gread h (gpointer_of_buffer_cell b i) == Seq.index (as_seq h b) (UInt32.v i)))
= ()

let gread_pointer_of_buffer_cell'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (length b)))
  (ensures (UInt32.v i < UInt32.v (length b) /\ Seq.index (as_seq h b) (UInt32.v i) == P.gread h (gpointer_of_buffer_cell b i)))
  [SMTPat (Seq.index (as_seq h b) (UInt32.v i))]
= ()

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)

let readable
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= P.buffer_readable h b

let readable_live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (readable h b))
  (ensures (live h b))
  [SMTPatOr [
    [SMTPat (readable h b)];
    [SMTPat (live h b)];
  ]]
= ()

let readable_gsingleton_buffer_of_pointer
  (#t: typ)
  (h: HS.mem)
  (p: pointer t)
: Lemma
  (ensures (readable h (gsingleton_buffer_of_pointer p) <==> P.readable h p))
  [SMTPat (readable h (gsingleton_buffer_of_pointer p))]
= ()

let readable_gbuffer_of_array_pointer
  (#len: array_length_t)
  (#t: typ)
  (h: HS.mem)
  (p: pointer (TArray len t))
: Lemma
  (requires True)
  (ensures (readable h (gbuffer_of_array_pointer p) <==> P.readable h p))
  [SMTPat (readable h (gbuffer_of_array_pointer p))]
= ()

let readable_gsub
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ readable h b))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (length b) /\ readable h (gsub b i len)))
  [SMTPat (readable h (gsub b i len))]
= ()

let readable_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (length b) /\ readable h b))
  (ensures (UInt32.v i < UInt32.v (length b) /\ P.readable h (gpointer_of_buffer_cell b i)))
  [SMTPat (P.readable h (gpointer_of_buffer_cell b i))]
= ()

let readable_intro
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (
    live h b /\ (
     forall (i: UInt32.t) .
     UInt32.v i < UInt32.v (length b) ==>
     P.readable h (gpointer_of_buffer_cell b i)
  )))
  (ensures (readable h b))
//  [SMTPat (buffer_readable h b)] // TODO: dubious pattern, may trigger unreplayable hints
= P.buffer_readable_intro h b

let read
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: HST.Stack (type_of_typ t)
  (requires (fun h -> UInt32.v i < UInt32.v (length b) /\ readable h b))
  (ensures (fun h v h' -> UInt32.v i < UInt32.v (length b) /\ h' == h /\ v == Seq.index (as_seq h b) (UInt32.v i)))
= P.read_buffer b i

let write
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (v: type_of_typ t)
: HST.Stack unit
  (requires (fun h -> UInt32.v i < UInt32.v (length b) /\ live h b))
  (ensures (fun h _ h' ->
    UInt32.v i < UInt32.v (length b) /\
    modifies_1 (gpointer_of_buffer_cell b i) h h' /\
    live h' b /\
    P.readable h' (gpointer_of_buffer_cell b i) /\
    Seq.index (as_seq h' b) (UInt32.v i) == v
  ))
= P.write_buffer b i v
