module FStar.BufferNG
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = FStar.Pointer

(* This module will help for the transition of some buffer-based code
   It tries to sidestep the following two issues:
   - the type of elements must be embeddable into P.typ
   - all elements must always be readable (no uninitialized data)
*)

let rec supported
  (t : P.typ)
: Tot bool
= match t with
  | P.TBase _ -> true
  | P.TStruct l -> struct_typ_supported l
  | _ -> false

and struct_typ_supported
  (l: list (string * P.typ))
: Tot bool
= match l with
  | [] -> true
  | (_, t) :: l' -> supported t && struct_typ_supported l'

let typ = (t: P.typ { supported t } )

unfold
let buffer
  (t: typ)
: Tot Type0
= P.buffer t

unfold
let live (#a: typ) (h: HS.mem) (b: buffer a) : GTot Type0 = 
  P.buffer_readable h b

unfold
let unused_in (#a: typ) (b: buffer a) (h: HS.mem) : GTot Type0 =
  P.buffer_unused_in b h

unfold
let length (#a: typ) (b: buffer a) : GTot nat =
  UInt32.v (P.buffer_length b)

unfold
let as_addr (#a: typ) (b: buffer a) : GTot nat =
  P.buffer_as_addr b

unfold
let frameOf (#a: typ) (b: buffer a) : GTot HH.rid =
  P.frameOf_buffer b

unfold
let as_seq (#a: typ) (h: HS.mem) (b: buffer a) : GTot (s: Seq.seq (P.type_of_typ a) { Seq.length s == length b } ) =
  P.buffer_as_seq h b

unfold
let equal (#a: typ) (h: HS.mem) (b: buffer a) (h' : HS.mem) (b' : buffer a) : GTot Type0 =
  as_seq h b == as_seq h' b'

unfold
let includes
  (#a: typ)
  (x y: buffer a)
: GTot Type0
= P.buffer_includes x y

let includes_live
  (#a: typ)
  (h: HS.mem)
  (x y : buffer a)
: Lemma
  (requires (x `includes` y /\ live h x))
  (ensures (live h y))
= P.buffer_includes_elim x y

let includes_as_seq #a h1 h2 (x: buffer a) (y: buffer a)
: Lemma
  (requires (x `includes` y /\ as_seq h1 x == as_seq h2 x))
  (ensures (as_seq h1 y == as_seq h2 y))
= P.buffer_includes_elim x y

let includes_trans #a (x y z: buffer a)
: Lemma
  (requires (x `includes` y /\ y `includes` z))
  (ensures (x `includes` z))
= P.buffer_includes_trans x y z

unfold
let disjoint (#a #a' : typ) (x: buffer a) (y: buffer a') : GTot Type0 =
  P.loc_disjoint (P.loc_buffer x) (P.loc_buffer y)

(* Disjointness is symmetric *)
let lemma_disjoint_symm #a #a' (x:buffer a) (y:buffer a') : Lemma
  (requires True)
  (ensures (disjoint x y <==> disjoint y x))
  [SMTPat (disjoint x y)]
  = ()

let lemma_disjoint_sub #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPatT (disjoint subx y); SMTPatT (includes x subx)]
  = P.buffer_includes_loc_includes x subx;
    P.loc_disjoint_includes (P.loc_buffer x) (P.loc_buffer y) (P.loc_buffer subx) (P.loc_buffer y)

let lemma_disjoint_sub' #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPatT (disjoint y subx); SMTPatT (includes x subx)]
  = ()

let lemma_live_disjoint #a #a' h (b:buffer a) (b':buffer a') : Lemma
  (requires (live h b /\ b' `unused_in` h))
  (ensures (disjoint b b'))
  [SMTPatT (disjoint b b'); SMTPatT (live h b)]
= ()

(** Concrete getters and setters *)
val create
  (#a:typ)
  (init: P.type_of_typ a)
  (len:UInt32.t)
: HST.StackInline (buffer a)
  (requires (fun h ->
    UInt32.v len > 0
  ))
  (ensures (fun (h0: HS.mem) b h1 ->
    UInt32.v len > 0 /\
    b `unused_in` h0 /\
    live h1 b /\
    length b == UInt32.v len /\
    frameOf b == h0.HS.tip /\
    P.modifies_0 h0 h1 /\
    as_seq h1 b == Seq.create (UInt32.v len) init
  ))
let create #a init len =
  let len : P.array_length_t = len in
  let content = P.screate (P.TArray len a) (Some (Seq.create (UInt32.v len) init)) in
  P.buffer_of_array_pointer content

unfold let p (#a:typ) (init:list (P.type_of_typ a)) : GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init < UInt.max_int 32)

unfold let q (#a:typ) (len:nat) (buf:buffer a) : GTot Type0 =
  normalize (length buf == len)

val createL
  (#a: typ)
  (init:list (P.type_of_typ a))
: HST.StackInline (buffer a)
  (requires (fun h -> p #a init))
  (ensures (fun (h0: HS.mem) b h1 ->
     let len = FStar.List.Tot.length init in
     len > 0 /\
     b `unused_in` h0 /\
     live h1 b /\
     length b == len /\
     frameOf b == h0.HS.tip /\
     P.modifies_0 h0 h1 /\
     as_seq h1 b == Seq.of_list init /\
     q #a len b
   ))
 
#set-options "--initial_fuel 1 --max_fuel 1" //the normalize_term (length init) in the pre-condition will be unfolded
	                                     //whereas the L.length init below will not

let createL #a init =
  let len : P.array_length_t = UInt32.uint_to_t (List.Tot.length init) in
  let s = Seq.of_list init in
  Seq.lemma_of_list_length s init;
  let content = P.screate (P.TArray len a) (Some s) in
  P.buffer_of_array_pointer content

#reset-options "--initial_fuel 0 --max_fuel 0"

val rcreate
  (#a: typ)
  (r:HH.rid)
  (init: P.type_of_typ a)
  (len:UInt32.t)
: HST.ST (buffer a)
  (requires (fun h ->
    HS.is_eternal_region r /\
    UInt32.v len > 0
  ))
  (ensures (fun (h0: HS.mem) b h1 ->
    b `unused_in` h0 /\
    live h1 b /\
    length b == UInt32.v len /\
    h1.HS.tip == h0.HS.tip /\
    P.modifies (P.loc_addresses r Set.empty) h0 h1 /\
    as_seq h1 b == Seq.create (UInt32.v len) init
  ))

let rcreate #a r init len =
  let len : P.array_length_t = len in
  let content = P.ecreate (P.TArray len a) r (Some (Seq.create (UInt32.v len) init)) in
  P.buffer_of_array_pointer content
  
val index
  (#a: typ)
  (b: buffer a)
  (n: UInt32.t)
: HST.Stack (P.type_of_typ a)
  (requires (fun h ->
    UInt32.v n < length b /\
    live h b
  ))
  (ensures (fun h0 z h1 ->
    UInt32.v n < length b /\
    h1 == h0 /\
    z == Seq.index (as_seq h0 b) (UInt32.v n)
  ))

let index #a b n =
  P.read_buffer b n

val upd
  (#a: typ)
  (b: buffer a)
  (n: UInt32.t)
  (z: P.type_of_typ a)
: HST.Stack unit
  (requires (fun h ->
    live h b /\
    UInt32.v n < length b
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    UInt32.v n < length b /\
    P.modifies (P.loc_pointer (P.gpointer_of_buffer_cell b n)) h0 h1 /\
    as_seq h1 b == Seq.upd (as_seq h0 b) (UInt32.v n) z
  ))

let upd #a b n z =
  let h0 = HST.get () in
  P.write_buffer b n z;
  let h1 = HST.get () in
  assert (Seq.equal (as_seq h1 b) (Seq.upd (as_seq h0 b) (UInt32.v n) z))

(* NOTE: Here I cannot fully respect the Buffer interface,
   because pure sub no longer exists, since it has been split
   into ghost gsub and stateful sub
 *)

unfold
let gsub
  (#a: typ)
  (b: buffer a)
  (i: UInt32.t)
  (len: UInt32.t)
: Ghost (buffer a)
  (requires (UInt32.v i + UInt32.v len <= length b))
  (ensures (fun _ -> True))
= P.gsub_buffer b i len

let sub
  (#a: typ)
  (b: buffer a)
  (i: UInt32.t)
  (len: UInt32.t)
: HST.Stack (buffer a)
  (requires (fun h ->
    live h b /\
    UInt32.v i + UInt32.v len <= length b
  ))
  (ensures (fun h0 b' h1 ->
    live h0 b /\
    UInt32.v i + UInt32.v len <= length b /\
    h1 == h0 /\
    b' == gsub b i len /\
    b `includes` b'
  ))
= P.sub_buffer b i len

let sub_sub
  (#a: typ)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len1 <= length b /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v len1
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= length b /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v len1 /\
    gsub (gsub b i1 len1) i2 len2 == gsub b (UInt32.add i1 i2) len2
  ))
= ()  

let sub_zero_length
  (#a: typ)
  (b: buffer a)
: Lemma
  (ensures (gsub b (UInt32.uint_to_t 0) (UInt32.uint_to_t (length b)) == b))
= ()

let lemma_sub_spec (#a:typ) (b:buffer a)
  (i:UInt32.t)
  (len:UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= length b /\
    live h b
  ))
  (ensures  (
    UInt32.v i + UInt32.v len <= length b /\
    live h (gsub b i len) /\
    as_seq h (gsub b i len) == Seq.slice (as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len)
  ))
  [SMTPatOr [
    [SMTPat (gsub b i len); SMTPatT (live h b)];
    [SMTPat (live h (gsub b i len))]
  ]]
  = Seq.lemma_eq_intro (as_seq h (gsub b i len)) (Seq.slice (as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len))

(* Same here *)

let goffset
  (#a: typ)
  (b: buffer a)
  (i: UInt32.t)
: Ghost (buffer a)
  (requires (UInt32.v i <= length b))
  (ensures (fun b' ->
    UInt32.v i <= length b /\
    b' == gsub b i (UInt32.sub (P.buffer_length b) i)
  ))
= P.gsub_buffer b i (UInt32.sub (P.buffer_length b) i)

let offset
  (#a:typ) 
  (b:buffer a)
  (i:UInt32.t)
: HST.Stack (buffer a)
  (requires (fun h0 ->
    live h0 b /\
    UInt32.v i <= length b
  ))
  (ensures (fun h0 b' h1 ->
    h1 == h0 /\
    UInt32.v i <= length b /\
    b' == goffset b i
  ))
= P.offset_buffer b i

let lemma_offset_spec
  (#a: typ)
  (b: buffer a)
  (i: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (
    UInt32.v i <= length b /\
    live h b
  ))
  (ensures (
    UInt32.v i <= length b /\
    as_seq h (goffset b i) == Seq.slice (as_seq h b) (UInt32.v i) (length b)
  ))
= ()






(*
  let content: reference (s:seq a{Seq.length s == v len}) =
     salloc (Seq.create (v len) init) in
  let b = MkBuffer len content 0ul len in
  let h = HST.get() in
  assert (Seq.equal (as_seq h b) (sel h b));
  b


(*
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
