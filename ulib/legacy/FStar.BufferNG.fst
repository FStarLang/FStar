(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.BufferNG
module HH = FStar.HyperStack
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
  | P.TStruct l -> struct_typ_supported l.P.fields
  | _ -> false

and struct_typ_supported
  (l: list (string & P.typ))
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
  [SMTPat (disjoint subx y); SMTPat (includes x subx)]
  = P.buffer_includes_loc_includes x subx;
    P.loc_disjoint_includes (P.loc_buffer x) (P.loc_buffer y) (P.loc_buffer subx) (P.loc_buffer y)

let lemma_disjoint_sub' #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPat (disjoint y subx); SMTPat (includes x subx)]
  = ()

let lemma_live_disjoint #a #a' h (b:buffer a) (b':buffer a') : Lemma
  (requires (live h b /\ b' `unused_in` h))
  (ensures (disjoint b b'))
  [SMTPat (disjoint b b'); SMTPat (live h b)]
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
    frameOf b == (HS.get_tip h0) /\
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
     frameOf b == (HS.get_tip h0) /\
     P.modifies_0 h0 h1 /\
     as_seq h1 b == Seq.seq_of_list init /\
     q #a len b
   ))
 
#set-options "--initial_fuel 1 --max_fuel 1" //the normalize_term (length init) in the pre-condition will be unfolded
	                                     //whereas the L.length init below will not

let createL #a init =
  let len : P.array_length_t = UInt32.uint_to_t (List.Tot.length init) in
  let s = Seq.seq_of_list init in
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
    HST.is_eternal_region r /\
    HST.witnessed (HST.region_contains_pred r) /\
    UInt32.v len > 0
  ))
  (ensures (fun (h0: HS.mem) b h1 ->
    b `unused_in` h0 /\
    live h1 b /\
    length b == UInt32.v len /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
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
    [SMTPat (gsub b i len); SMTPat (live h b)];
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

val eqb: #a:typ -> b1:buffer a -> b2:buffer a
  -> len:UInt32.t
  -> HST.ST bool
    (requires (fun h ->
      hasEq (P.type_of_typ a) /\
      UInt32.v len <= length b1 /\
      UInt32.v len <= length b2 /\
      live h b1 /\
      live h b2
    ))
    (ensures  (fun h0 z h1 ->
      h1 == h0 /\
      UInt32.v len <= length b1 /\
      UInt32.v len <= length b2 /\
      (z <==> equal h0 (gsub b1 0ul len) h0 (gsub b2 0ul len))
    ))

let eqb #a b1 b2 len =
  P.buffer_contents_equal b1 b2 len

(* JP: if the [val] is not specified, there's an issue with these functions
 * taking an extra unification parameter at extraction-time... *)
val op_Array_Access: #a:typ -> b:buffer a -> n:UInt32.t -> HST.Stack (P.type_of_typ a)
     (requires (fun h -> UInt32.v n<length b /\ live h b))
     (ensures (fun h0 z h1 -> h1 == h0 /\
       UInt32.v n<length b /\
       z == Seq.index (as_seq h0 b) (UInt32.v n)))
let op_Array_Access #a b n = index #a b n

val op_Array_Assignment: #a:typ -> b:buffer a -> n:UInt32.t -> z:P.type_of_typ a -> HST.Stack unit
  (requires (fun h -> live h b /\ UInt32.v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ UInt32.v n < length b
    /\ P.modifies (P.loc_pointer (P.gpointer_of_buffer_cell b n)) h0 h1
    /\ as_seq h1 b == Seq.upd (as_seq h0 b) (UInt32.v n) z ))
let op_Array_Assignment #a b n z = upd #a b n z

val live_slice_middle
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= length b /\
    live h (gsub b 0ul i) /\
    live h (gsub b i len) /\ (
    let off = UInt32.add i len in
    live h (gsub b off (UInt32.sub (P.buffer_length b) off))
  )))
  (ensures (live h b))
  [SMTPat (live h (gsub b i len))]

let live_slice_middle #t b i len h =
  P.buffer_readable_gsub_merge b i len h

(** Corresponds to memcpy *)
val blit: #t:typ
  -> a:buffer t
  -> idx_a:UInt32.t
  -> b:buffer t{disjoint a b}
  -> idx_b:UInt32.t
  -> len:UInt32.t{UInt32.v idx_a + UInt32.v len <= length a /\ UInt32.v idx_b + UInt32.v len <= length b}
  -> HST.Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures  (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a /\ P.modifies (P.loc_buffer (gsub b idx_b len)) h0 h1
      /\ Seq.slice (as_seq h1 b) (UInt32.v idx_b) (UInt32.v idx_b + UInt32.v len) ==
        Seq.slice (as_seq h0 a) (UInt32.v idx_a) (UInt32.v idx_a + UInt32.v len)
      /\ Seq.slice (as_seq h1 b) 0 (UInt32.v idx_b) ==
        Seq.slice (as_seq h0 b) 0 (UInt32.v idx_b)
      /\ Seq.slice (as_seq h1 b) (UInt32.v idx_b+UInt32.v len) (length b) ==
        Seq.slice (as_seq h0 b) (UInt32.v idx_b+UInt32.v len) (length b) ))

let blit #t a idx_a b idx_b len =
  if len = 0ul
  then ()
  else begin
    let h0 = HST.get () in
    P.copy_buffer_contents a idx_a b idx_b len;
    let h1 = HST.get () in
    P.buffer_readable_modifies_gsub b idx_b len h0 h1 (P.loc_buffer (P.gsub_buffer b idx_b len));
    assert (let g = (gsub b (UInt32.add idx_b len) (UInt32.sub (P.buffer_length b) (UInt32.add idx_b len))) in as_seq h1 g == as_seq h0 g);
    assert (as_seq h1 (gsub b idx_b len) == as_seq h0 (gsub a idx_a len));
    assert (let g = gsub b 0ul idx_b in as_seq h1 g == as_seq h0 g)
  end

(** Corresponds to memset *)
val fill: #t:typ
  -> b:buffer t
  -> z: P.type_of_typ t
  -> len:UInt32.t{UInt32.v len <= length b}
  -> HST.Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\
      P.modifies (P.loc_buffer (gsub b 0ul len)) h0 h1
      /\ Seq.slice (as_seq h1 b) 0 (UInt32.v len) == Seq.create (UInt32.v len) z
      /\ Seq.slice (as_seq h1 b) (UInt32.v len) (length b) ==
        Seq.slice (as_seq h0 b) (UInt32.v len) (length b) ))

let fill #t b z len =
  let h0 = HST.get () in
  P.fill_buffer b 0ul len z;
  let h1 = HST.get () in
  assert (as_seq h1 (gsub b 0ul len) == Seq.slice (as_seq h1 b) 0 (UInt32.v len));
  assert (let g = gsub b len (UInt32.sub (P.buffer_length b) len) in as_seq h1 g == as_seq h0 g)
