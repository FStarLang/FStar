(*--build-config
    options:--admit_fsi Set --admit_fsi Seq;
    variables:LIB=../../../lib;
    other-files:$LIB/classical.fst $LIB/ext.fst $LIB/set.fsi $LIB/seq.fsi $LIB/seqproperties.fst
  --*)

module Platform.Bytes

val repr_bytes : nat -> Tot nat
let repr_bytes n =
    if n < 256 then 1
    else if n < 65536 then 2
    else if n < 16777216 then 3
    (*else if n < 4294967296 then 4
    else if n < 1099511627776 then 5
    else if n < 281474976710656 then 6
    else if n < 72057594037927936 then 7    *)
    else 8
(* NS:
   The two assumes below were previously defined as axioms.
	 They are evil! They pollute the global environment and
	 slow down verification enormously.
	 I've made them assumed lemmas; if you want to
	 make use of these axioms, call the lemmas as needed in the context.
*)
(* SZ: No longer needed because we have a definition? *)
(*
val lemma_repr_bytes_values: n:nat ->
    Lemma (ensures
       			  ( n < 256 <==> repr_bytes n = 1 )
               /\ ( (n < 65536 /\ n >= 256 ) <==> repr_bytes n = 2 )
               /\ ( (n >= 65536 /\ n < 16777216) <==> repr_bytes n = 3 )
               /\ ( (n >= 16777216 /\ n < 4294967296) <==> repr_bytes n = 4 )
               /\ ( (n >= 4294967296 /\ n < 1099511627776) <==> repr_bytes n = 5 )
               /\ ( (n >= 1099511627776 /\ n < 281474976710656) <==> repr_bytes n = 6 )
               /\ ( (n >= 281474976710656 /\ n < 72057594037927936) <==> repr_bytes n = 7 )
               )
let lemma_repr_bytes_values n = ()

val lemma_repr_bytes_monotone: a:nat -> b:nat ->
    Lemma (ensures (a <= b ==> repr_bytes a <= repr_bytes b))
let lemma_repr_bytes_monotone a b = ()
*)

type byte = uint8
type cbytes = string
type bytes = Seq.seq byte

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

val abyte : (byte -> Tot bytes)
let abyte (b:byte) = Seq.create 1 b

val abyte2 : (byte * byte) -> Tot bytes
let abyte2 (b1, b2) = Seq.append (Seq.create 1 b1) (Seq.create 1 b2)

(*@ assume val get_cbytes : (a:bytes -> (b:cbytes){B (a) = b}) @*)
assume val get_cbytes : (bytes -> Tot cbytes)

val cbyte : b:bytes{Seq.length b > 0} -> Tot byte
let cbyte b = Seq.index b 0

val cbyte2 : b:bytes{Seq.length b >= 2} -> Tot (byte * byte)
let cbyte2 b = (Seq.index b 0, Seq.index b 1)

(*@ function assume val BLength : (cbytes -> int) @*)

(*@ function assume val Length : (bytes -> int) @*)

(*@  assume (!x. (!y. BLength (C_bop_ArrayAppend (x, y)) = C_bop_Addition (BLength (x), BLength (y)))) @*)

(*@  assume (!x. Length (x) = BLength (B (x))) @*)

(*@ assume val createBytes : (l:int -> ((v:int){C_pr_LessThanOrEqual(0, v) /\ C_pr_LessThan(v, 256)} -> (;l) lbytes)) @*)
val createBytes : nat -> byte -> Tot bytes
let createBytes l b = Seq.create l b

(*@ assume val equalBytes : (b0:bytes -> (b1:bytes -> (r:bool){r = True /\ B (b0) = B (b1) \/ r = False /\ B (b0) <> B (b1)})) @*)
assume val equalBytes : bytes -> bytes -> Tot bool
(*@ assume val xor : (bytes -> (bytes -> (nb:nat -> (b3:bytes){Length (b3) = nb}))) @*)
assume val xor : bytes -> bytes -> nat -> Tot bytes

val split: b:bytes -> n:nat{n <= Seq.length b} -> Tot (x:(bytes * bytes) {Seq.length (fst (x))= n /\ Seq.length (snd (x)) == (Seq.length b) - n }) //(lbytes n * lbytes (length b - n))
let split b n =
  SeqProperties.split b n

(*@ assume val split2 : (b:bytes -> (i:nat -> ((j:nat){C_pr_GreaterThanOrEqual(Length (b), C_bop_Addition (i, j))} -> (b1:bytes * b2:bytes * b3:bytes){Length (b1) = i /\ Length (b2) = j /\ B (b) = C_bop_ArrayAppend (B (b1), C_bop_ArrayAppend (B (b2), B (b3)))}))) @*)
assume val split2 : b:bytes -> n1:nat{n1 <= Seq.length b} -> n2:nat{n1 + n2 <= Seq.length b} -> Tot (lbytes n1 * lbytes n2 * lbytes (length b - n1 - n2))
(*@  assume (!x. C_bop_ArrayAppend (x, C_array_of_list C_op_Nil ()) = x) @*)

(*@  assume (!b1. (!b2. (!c1. (!c2. C_bop_ArrayAppend (b1, b2) = C_bop_ArrayAppend (c1, c2) /\ BLength (b1) = BLength (c1) => b1 = c1 /\ b2 = c2)))) @*)

(*@  assume (!b1. (!b2. (!c1. (!c2. C_bop_ArrayAppend (b1, b2) = C_bop_ArrayAppend (c1, c2) /\ BLength (b2) = BLength (c2) => b1 = c1 /\ b2 = c2)))) @*)

(*@  assume (!b1. (!b2. (!b3. C_bop_ArrayAppend (C_bop_ArrayAppend (b1, b2), b3) = C_bop_ArrayAppend (b1, C_bop_ArrayAppend (b2, b3))))) @*)

(*@ function assume val IntBytes : ((int * int) -> bytes) @*)

assume val bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} -> Tot (lbytes l)
assume val int_of_bytes : b:bytes{Seq.length b <= 8} -> 
    Tot (n:nat{repr_bytes n <= Seq.length b /\ b=bytes_of_int (Seq.length b) n})

(*@ assume val int_of_bytes : ((b:bytes){C_pr_LessThanOrEqual(Length (b), 8)} -> (i:nat){b = IntBytes (Length (b), i) /\ Length (b) = 1 => C_pr_LessThanOrEqual(0, i) /\ C_pr_LessThan(i, 256)}) @*)

(*@  assume (!l. (!i. Length (IntBytes (l, i)) = l)) @*)

(*@  assume (!l. (!i0. (!i1. IntBytes (l, i0) = IntBytes (l, i1) => i0 = i1))) @*)

(*@ function assume val Utf8 : (string -> bytes) @*)

(*@ assume val utf8 : (s:string -> (b:bytes){b = Utf8 (s)}) @*)
assume val utf8 : string -> Tot bytes
(*@ assume val iutf8 : (b:bytes -> (s:string){b = Utf8 (s)}) @*)
assume val iutf8_opt : bytes -> Tot (option string)
assume val iutf8 : m:bytes -> s:string{utf8 s == m}
(*@  assume (!x. (!y. Utf8 (x) = Utf8 (y) => x = y)) @*)

assume val byte_of_int: i:int{0 <= i /\ i < 256} -> Tot byte
