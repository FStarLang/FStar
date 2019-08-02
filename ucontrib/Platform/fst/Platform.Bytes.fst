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
module Platform.Bytes

assume val repr_bytes : nat -> GTot (n:nat{n>0})
(* Integer literals are currently extracted to int32, rather than bigint, so the definition below
   breaks extraction:
   Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
   int_of_string

   Also, defining repr_bytes n <= 8 for all n is dubious
*)
(*
let repr_bytes n =
    if n < 256 then 1
    else if n < 65536 then 2
    else if n < 16777216 then 3
    else if n < 4294967296 then 4
    else if n < 1099511627776 then 5
    else if n < 281474976710656 then 6
    else if n < 72057594037927936 then 7
    else 8
*)
(* NS:
   The two assumes below were previously defined as axioms.
	 They are evil! They pollute the global environment and
	 slow down verification enormously.
	 I've made them assumed lemmas; if you want to
	 make use of these axioms, call the lemmas as needed in the context.
*)
assume val lemma_repr_bytes_values: n:nat ->
  Lemma (   ( n < 256 <==> repr_bytes n = 1 )
         /\ ( (n >= 256 /\ n < 65536) <==> repr_bytes n = 2 )
         /\ ( (n >= 65536 /\ n < 16777216) <==> repr_bytes n = 3 )
         /\ ( (n >= 16777216 /\ n < 4294967296) <==> repr_bytes n = 4 )
         /\ ( (n >= 4294967296 /\ n < 1099511627776) <==> repr_bytes n = 5 )
         /\ ( (n >= 1099511627776 /\ n < 281474976710656) <==> repr_bytes n = 6 )
         /\ ( (n >= 281474976710656 /\ n < 72057594037927936) <==> repr_bytes n = 7 )
         /\ ( (n >= 72057594037927936 /\ n < 18446744073709551616) <==> repr_bytes n = 8 ) )

unfold let byte:Type0 = FStar.UInt8.t
type cbytes = string
(* abstract *) type bytes = Seq.seq byte

(* AR: adding this *)
assume HasEq_bytes: hasEq bytes

val seq_of_bytes: b:bytes -> GTot (Seq.seq byte)
let seq_of_bytes b = b

val op_At_Bar: bytes -> bytes -> Tot bytes
let op_At_Bar (b1:bytes) (b2:bytes) = Seq.append b1 b2

(*@ function val B : (bytes -> byte array) @*)

(*@ assume val length : (b:bytes -> (l:nat){Length (b) = l}) @*)
val length : bytes -> Tot nat
let length b = Seq.length b

(*@ type (l:nat) lbytes = (b:bytes){Length (b) = l} @*)
type lbytes (l:nat) = b:bytes{length b = l}

(*@ val empty_bytes : (b:bytes){B (b) = C_array_of_list C_op_Nil ()} @*)
val empty_bytes : lbytes 0
let empty_bytes = Seq.create 0 0uy

(*@ assume val abytes : (b:cbytes -> (a:bytes){B (a) = b}) @*)
assume val abytes : (cbytes -> Tot bytes)
(*@ assume val abyte : (b:byte -> (a:bytes){B (a) = C_array_of_list C_op_ColonColon (b, C_op_Nil ())}) @*)

val abyte : (FStar.UInt8.t -> Tot bytes)
let abyte b = Seq.create 1 b

val abyte2 : (FStar.UInt8.t * FStar.UInt8.t) -> Tot bytes
let abyte2 (b1, b2) = Seq.append (Seq.create 1 b1) (Seq.create 1 b2)

(*@ assume val get_cbytes : (a:bytes -> (b:cbytes){B (a) = b}) @*)
assume val get_cbytes : (bytes -> Tot cbytes)

val cbyte : b:bytes{Seq.length b > 0} -> Tot FStar.UInt8.t
let cbyte b = Seq.index b 0

val cbyte2 : b:bytes{Seq.length b >= 2} -> Tot (FStar.UInt8.t * FStar.UInt8.t)
let cbyte2 b = (Seq.index b 0, Seq.index b 1)

val index : b:bytes -> i:nat{Seq.length b > i} -> Tot FStar.UInt8.t
let index b i = Seq.index b i

(*@ function assume val BLength : (cbytes -> int) @*)

(*@ function assume val Length : (bytes -> int) @*)

(*@  assume (!x. (!y. BLength (C_bop_ArrayAppend (x, y)) = C_bop_Addition (BLength (x), BLength (y)))) @*)

(*@  assume (!x. Length (x) = BLength (B (x))) @*)

(*@ assume val createBytes : (l:int -> ((v:int){C_pr_LessThanOrEqual(0, v) /\ C_pr_LessThan(v, 256)} -> (;l) lbytes)) @*)
val createBytes : l:nat -> FStar.UInt8.t -> Tot (lbytes l)
let createBytes l b = Seq.create l b

// TODO: not implemented in ML
val initBytes: l:nat -> (i:nat {i<l} -> Tot byte) -> Tot (lbytes l)
let initBytes l f = Seq.init l f


(*@ assume val equalBytes : (b0:bytes -> (b1:bytes -> (r:bool){r = True /\ B (b0) = B (b1) \/ r = False /\ B (b0) <> B (b1)})) @*)
assume val equalBytes : b1:bytes -> b2:bytes -> Tot (b:bool{b = (b1=b2)})
(*@ assume val xor : (bytes -> (bytes -> (nb:nat -> (b3:bytes){Length (b3) = nb}))) @*)

assume val xor: l:nat -> lbytes l -> lbytes l -> Tot (lbytes l)
// consider making the length implicit

val split: b:bytes -> n:nat{n <= Seq.length b} ->
  Tot (x:(bytes * bytes) {Seq.length (fst (x))= n /\ Seq.length (snd (x)) == (Seq.length b) - n }) //(lbytes n * lbytes (length b - n))
//val split: bytes -> nat -> Tot (bytes * bytes)
let split b (n:nat { n <= Seq.length b}) = Seq.split b n

val lemma_split : s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures ((fst (split s i)) @| (snd (split s i)) = s))
let lemma_split s i =
  cut (Seq.equal ((fst (split s i)) @| (snd (split s i)))  s)

val split_eq: s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Pure
  (x:(bytes * bytes){length (fst x) = i && length (snd x) = length s - i})
  (requires True)
  (ensures (fun x -> ((fst x) @| (snd x) = s)))
let split_eq s i =
  let x = split s i in
  lemma_split s i;
  x

val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes -> t2:bytes {Seq.length s1 = Seq.length t1 \/ Seq.length s2 = Seq.length t2} ->
  Lemma (requires (Seq.equal (Seq.append s1 s2) (Seq.append t1 t2)))
        (ensures (Seq.equal s1 t1 /\ Seq.equal s2 t2))
let lemma_append_inj s1 s2 t1 t2 = admit() (* CH: this used to fail *)

let append_empty_bytes_l (l: bytes): Lemma (ensures (empty_bytes @| l == l)) =
  Seq.append_empty_l l

let append_empty_bytes_r (l: bytes): Lemma (ensures (l @| empty_bytes == l)) =
  Seq.append_empty_r l
  
let append_assoc (l1 l2 l3: bytes): Lemma
  (ensures ((l1 @| l2) @| l3 == l1 @| (l2 @| l3))) =
  Seq.append_assoc l1 l2 l3

(*@ assume val split2 : (b:bytes -> (i:nat -> ((j:nat){C_pr_GreaterThanOrEqual(Length (b), C_bop_Addition (i, j))} -> (b1:bytes * b2:bytes * b3:bytes){Length (b1) = i /\ Length (b2) = j /\ B (b) = C_bop_ArrayAppend (B (b1), C_bop_ArrayAppend (B (b2), B (b3)))}))) @*)
assume val split2 : b:bytes -> n1:nat{n1 <= Seq.length b} -> n2:nat{n1 + n2 <= Seq.length b} -> Tot (lbytes n1 * lbytes n2 * lbytes (length b - n1 - n2))
(*@  assume (!x. C_bop_ArrayAppend (x, C_array_of_list C_op_Nil ()) = x) @*)

(*@  assume (!b1. (!b2. (!c1. (!c2. C_bop_ArrayAppend (b1, b2) = C_bop_ArrayAppend (c1, c2) /\ BLength (b1) = BLength (c1) => b1 = c1 /\ b2 = c2)))) @*)

(*@  assume (!b1. (!b2. (!c1. (!c2. C_bop_ArrayAppend (b1, b2) = C_bop_ArrayAppend (c1, c2) /\ BLength (b2) = BLength (c2) => b1 = c1 /\ b2 = c2)))) @*)

(*@  assume (!b1. (!b2. (!b3. C_bop_ArrayAppend (C_bop_ArrayAppend (b1, b2), b3) = C_bop_ArrayAppend (b1, C_bop_ArrayAppend (b2, b3))))) @*)

(*@ function assume val IntBytes : ((int * int) -> bytes) @*)

assume val bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} -> Tot (lbytes l)
assume val int_of_bytes : b:bytes ->
    Tot (n:nat{repr_bytes n <= Seq.length b /\
             (Seq.length b = 1 ==> n < 256) /\
             b=bytes_of_int (Seq.length b) n})

assume val int_of_bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} ->
    Lemma (n = int_of_bytes (bytes_of_int l n))

(*@ assume val int_of_bytes : ((b:bytes){C_pr_LessThanOrEqual(Length (b), 8)} -> (i:nat){b = IntBytes (Length (b), i) /\ Length (b) = 1 => C_pr_LessThanOrEqual(0, i) /\ C_pr_LessThan(i, 256)}) @*)

(*@  assume (!l. (!i. Length (IntBytes (l, i)) = l)) @*)

(*@  assume (!l. (!i0. (!i1. IntBytes (l, i0) = IntBytes (l, i1) => i0 = i1))) @*)

(*@ function assume val Utf8 : (string -> bytes) @*)

(*@ assume val utf8 : (s:string -> (b:bytes){b = Utf8 (s)}) @*)
assume val utf8 : string -> Tot bytes
(*@ assume val iutf8 : (b:bytes -> (s:string){b = Utf8 (s)}) @*)
assume val iutf8_opt : m:bytes -> Tot (option (s:string{utf8 s = m}))
assume val iutf8 : m:bytes -> s:string{utf8 s = m}
(*@  assume (!x. (!y. Utf8 (x) = Utf8 (y) => x = y)) @*)

// Pretty printing of bytes for debugging
assume val print_bytes: bytes -> Tot string

val byte_of_int: n:nat{n < 256} -> Tot byte
let byte_of_int n =
  lemma_repr_bytes_values n;
  Seq.index (bytes_of_int 1 n) 0

// No definition for these: they're only meant to be used to write tests within
// F*.
assume val bytes_of_hex: string -> Tot bytes
assume val hex_of_bytes: bytes -> Tot string
assume val string_of_hex: string -> Tot string
assume val hex_of_string: string -> Tot string
