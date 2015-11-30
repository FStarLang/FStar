(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Bigint;
  other-files:classical.fst ext.fst set.fsi seq.fsi seqproperties.fst heap.fst st.fst all.fst arr.fst ghost.fst axiomatic.fst intlib.fst limb.fst;
  --*)

module Bigint

open IntLib
open Limb
open FStar.Seq
open FStar.SeqProperties
open FStar.All
open FStar.ST
open FStar.Heap
open FStar.Array
open FStar.Ghost

(* TODO : stabilize the type definitions *)
(* Int types *)
type int64 = int
type integer = int
type u8 = int

let ocaml63 = 63

(* Maps the index of the integer data to the theoretic bit size of the cell *)
type template = nat -> Tot (n:pos{ n < ocaml63 })
type template_const = t:template{ forall (n:nat). t n = t 0 }

(* Sized integer *)
// A potential ghost version
//type tint (max:nat) = (size:erased nat{ reveal size < max } & content:int{ Bitsize content (reveal size) })
type tint (max:nat) = (size:nat{ size < max } & content:int{ Bitsize content size })

(* Sized ST array *)
type tarray (max:nat) = array (tint max)

(* Big integer type *)
private type bigint = 
  | Bigint63 : data:tarray ocaml63 -> t:template -> bigint

(* Constructor *)
val create: tarray ocaml63 -> template -> Tot bigint
let create data t = Bigint63 data t

val wordSize: bigint -> Tot pos
let wordSize b = 
  match b with
    | Bigint63 _ _ -> ocaml63

type SameFormat (ha:heap) (hb:heap) (a:bigint) (b:bigint) = 
  (contains ha (Bigint63.data a) /\ contains hb (Bigint63.data b))
  /\ (Bigint63.t a = Bigint63.t b) 
  /\ (Seq.length (sel ha (Bigint63.data a)) = Seq.length (sel hb (Bigint63.data b)))

type inHeap (h:heap) (b:bigint) = b2t (contains h (Bigint63.data b))

(* Getters *)

(* Logical only *)
assume logic val getLength : 
	       h:heap -> b:bigint{ inHeap h b } -> 
	       Tot (len:nat{ len = Seq.length (sel h (Bigint63.data b)) })

assume logic val getSize : 
	       h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } -> 
	       Tot (s:nat{s = dfst (Seq.index (sel h (Bigint63.data b)) i) /\  s < (wordSize b)})

assume logic val lgetSize:
  h:heap -> b:bigint{ inHeap h b } -> i:erased nat{ reveal i < getLength h b } -> 
  Tot (s:erased nat{reveal s = dfst (Seq.index (sel h (Bigint63.data b)) (reveal i)) /\ reveal s < (wordSize b)})  

assume logic val getValue :
	       h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } ->
	       Tot (v:int{ v = dsnd (Seq.index (sel h (Bigint63.data b)) i)})

assume logic val getContent :
	       h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } ->
	       Tot (v:tint (wordSize b){ v = (Seq.index (sel h (Bigint63.data b)) i)})

assume logic val getData:
  b:bigint ->
  Tot (t:tarray ocaml63{t = Bigint63.data b})  

val size_of_value_lemma:
  h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } -> 
  Lemma
    (requires (True))
    (ensures (Bitsize (getValue h b i) (getSize h b i)))
let size_of_value_lemma h b i = ()

val lsize_of_value_lemma:
  h:heap -> b:bigint{ inHeap h b } -> i:erased nat{ reveal i < getLength h b } -> 
  Lemma
    (requires (True))
    (ensures (Bitsize (getValue h b (reveal i)) (getSize h b (reveal i))))
let lsize_of_value_lemma h b i = ()


(* Concrete getters *)
val get_content: 
  b:bigint -> i:nat ->
  ST (tint (wordSize b))
     (requires (fun h -> (inHeap h b)
			 /\ (i < getLength h b)))
     (ensures (fun h0 v h1 -> (inHeap h1 b)
			      /\ (h1==h0)
			      /\ (i < getLength h1 b)
			      /\ (v = getContent h1 b i)))
let get_content b i =
  match b with 
  | Bigint63 data t ->
     FStar.Array.index data i

val get_length:
  b:bigint ->
  ST nat
     (requires (fun h -> (inHeap h b)))
     (ensures (fun h0 l h1 -> (h0 == h1) 
			      /\ (inHeap h0 b)
			      /\ (l = getLength h0 b)))
let get_length b =
  match b with
  | Bigint63 data t -> FStar.Array.length data		 

val get: 
  b:bigint -> n:nat -> 
  ST int
     (requires (fun h -> inHeap h b /\ n < getLength h b))
     (ensures (fun h0 v h1 -> (h0==h1)
			      /\ (inHeap h1 b)
			      /\ (n < getLength h1 b)
			      /\ (v = getValue h1 b n /\ Bitsize v (getSize h1 b n))
      ))
let get b n =
  match b with
  | Bigint63 data t ->
     let (|size,v|) = (FStar.Array.index data n) in v

val getTemplate: bigint -> Tot template
let getTemplate b =
  match b with
  | Bigint63 _ t -> t

(* Setter *)
val updateBigint:
  b:bigint -> idx:nat -> v:tint ocaml63 -> 
  ST unit
     (requires (fun h -> (contains h (Bigint63.data b))
			 /\ (idx < Seq.length (sel h (Bigint63.data b)))))
     (ensures (fun h0 u h1 -> 
	       (idx < Seq.length (sel h0 (Bigint63.data b)))
               /\ (contains h1 (Bigint63.data b))
	       /\ (h1==Heap.upd h0 (Bigint63.data b) (Seq.upd (sel h0 (Bigint63.data b)) idx v))	      ))
let updateBigint b idx v =
  match b with
  | Bigint63 data _ ->
     FStar.Array.upd data idx v

val update_bigint_lemma:
  h0:heap -> h1:heap -> b:bigint{ inHeap h1 b /\ inHeap h0 b }  -> idx:nat{ idx < getLength h0 b } -> v:tint ocaml63 -> 
  Lemma
    (requires (h1 == Heap.upd h0 (Bigint63.data b) (Seq.upd (sel h0 (Bigint63.data b)) idx v)))
    (ensures ( (getLength h1 b = getLength h0 b)
	       /\ (getValue h1 b idx = dsnd v) 
	       /\ (getSize h1 b idx = dfst v)
	       /\ (forall (i:nat). (i < getLength h1 b /\ i <> idx) ==> 
		     (getValue h1 b i = getValue h0 b i /\ getSize h1 b i = getSize h0 b i) )
	       /\ (modifies !{Bigint63.data b} h0 h1) ))
let update_bigint_lemma h0 h1 b idx v = ()

type EqualBigint (a:bigint) (b:bigint) (ha:heap) (hb:heap) =
  (contains ha (Bigint63.data a)) 
  /\ (contains hb (Bigint63.data b))
  /\ (getLength ha a = getLength hb b)
  /\ (forall (i:nat). i < getLength ha a ==> getValue ha a i = getValue hb b i)
  /\ (forall (i:nat). i < getLength ha a ==> getSize ha a i = getSize hb b i)
  /\ (Bigint63.t a = getTemplate b)

opaque val copy:
  a:bigint ->
  ST bigint
     (requires (fun h -> inHeap h a /\ getLength h a > 0))
     (ensures (fun h0 b h1 ->
       (inHeap h0 a)
       /\ (inHeap h1 b)
       /\ not(contains h0 (Bigint63.data b))
       /\ (EqualBigint a b h0 h1)
       /\ (modifies !{} h0 h1)
     ))
let copy a =
  Bigint63 (FStar.Array.copy (Bigint63.data a)) (Bigint63.t a)

(* Normalized big integer type *)
type Normalized (h:heap) (b:bigint{ inHeap h b })  =
  (forall (n:nat). n < getLength h b ==> getSize h b n <= (Bigint63.t b) n)

type IsNull (h:heap) (b:bigint{ inHeap h b }) =
  (forall (n:nat). n < getLength h b ==> getValue h b n = 0)

(* Zeros and ones *)
val zero_tint: z:tint ocaml63{ dsnd z = 0 }
let zero_tint = (|0, 0|)

val one_tint: z:tint ocaml63{ dsnd z = 1 }
let one_tint = (|1, 1|)

let mk_zero_bigint size template =
  Bigint63 (FStar.Array.create size zero_tint) template

let mk_one_bigint size template =
  let one = Bigint63 (FStar.Array.create size zero_tint) template in
  updateBigint one 0 one_tint;
  one

val mk_tint: a:bigint -> size:nat{ size < wordSize a } -> value:int{ Bitsize value size } -> 
	     Tot (z:tint (wordSize a))
let mk_tint a size value =
  match a with
  | Bigint63 _ _ -> 
     (|size, value|)

opaque val extend :
  a:bigint -> len:pos ->
  ST bigint
    (requires (fun h ->
      (inHeap h a)
      /\ (len >= getLength h a)
     ))
    (ensures (fun h0 b h1 ->
      (inHeap h0 a)
      /\ (inHeap h1 b)
      /\ (Bigint63.data b <> Bigint63.data a)
      /\ (modifies !{} h0 h1)
      /\ (len >= getLength h0 a)
      /\ (getLength h1 b = len)
      /\ (Seq.Eq (sel h0 (Bigint63.data a)) (Seq.slice (sel h1 (Bigint63.data b)) 0 (getLength h0 a)))
      /\ (forall (i:nat). (i >= getLength h0 a /\ i < len)
	  ==> Seq.index (sel h1 (Bigint63.data b)) i = zero_tint)
     ))
let extend a len =
  let len_a = get_length a in
  let b = Bigint.mk_zero_bigint len (Bigint63.t a) in
  FStar.Array.blit (Bigint63.data a) 0 (Bigint63.data b) 0 len_a;
  b

(* TODO : implement *)
assume opaque val blit:
  a:bigint -> b:bigint ->
  ST unit
    (requires (fun h -> 
      (inHeap h a) /\ (inHeap h b)
      /\ (getTemplate a = getTemplate b)
      /\ (getLength h b >= getLength h a)
      ))
    (ensures (fun h0 _ h1 ->
      (inHeap h0 a) /\ (inHeap h0 b)
      /\ (inHeap h1 a) /\ (inHeap h1 b)
      /\ (getTemplate a = getTemplate b)
      /\ (getLength h0 b >= getLength h0 a)
      /\ (getLength h0 b = getLength h1 b)
      /\ (getLength h1 a = getLength h0 a)
      /\ (modifies !{getData b} h0 h1)
      /\ (Seq.Eq (Seq.slice (sel h1 (getData b)) 0 (getLength h0 a)) (sel h0 (getData a)))
      /\ (Seq.Eq (Seq.slice (sel h1 (getData b)) (getLength h0 a) (getLength h1 b)) (Seq.create (getLength h0 b - getLength h0 a) zero_tint))
      ))

  

#reset-options

val populate_tarray : 
  t:array int -> templ:template -> max:nat{forall (i:nat). templ i < max} -> 
  len:nat -> a:tarray max ->
  ST unit
    (requires (fun h ->
      (contains h t)
      /\ (contains h a)
      /\ (len <= Seq.length (sel h t))
      /\ (len <= Seq.length (sel h a))
      /\ (forall (i:nat). i < len ==> Bitsize (Seq.index (sel h t) i) (templ i))
    ))
    (ensures (fun h0 _ h1 -> 
      (contains h0 t)
      /\ (contains h0 a)
      /\ (len <= Seq.length (sel h0 t))
      /\ (len <= Seq.length (sel h0 a))
      /\ (forall (i:nat). i < len ==> Bitsize (Seq.index (sel h0 t) i) (templ i))
    ))
let rec populate_tarray t templ max len a = 
  match len with
  | 0 -> ()
  | _ -> 
     let i = len - 1 in
     let v = FStar.Array.index t i in
     FStar.Array.upd a i (|templ i, v|);
     populate_tarray t templ max (len-1) a

val mk_tarray : 
  t:array int -> templ:template -> max:pos{ forall (i:nat). templ i < max } ->
  ST (tarray max)
    (requires (fun h -> 
      (contains h t)
    ))
    (ensures (fun h0 s h1 -> 
      (contains h0 t)
    ))
let mk_tarray t tmpl max =
  let len = FStar.Array.length t in
  let a = FStar.Array.create len (|0,0|) in
  populate_tarray t tmpl max 0 a;
  a

val populate_array : 
  max:pos -> t:tarray max -> len:nat -> a:array int ->
  ST unit
    (requires (fun h -> 
      (contains h t)
      /\ (contains h a)
      /\ (Seq.length (sel h t) >= len)
      /\ (Seq.length (sel h a) >= len)
      
      ))
    (ensures (fun h0 _ h1 -> 
      (contains h0 t)
      /\ (contains h0 a)
      /\ (Seq.length (sel h0 t) >= len)
      /\ (Seq.length (sel h0 a) >= len)
    ))
let rec populate_array max t len a =
  match len with
  | 0 -> ()
  | _ -> 
     let i = len - 1 in
     let ti = FStar.Array.index t i in
     FStar.Array.upd a i (dsnd ti);
     populate_array max t (len-1) a

val mk_array : 
  max:pos -> t:tarray max ->
  ST (array int)
    (requires (fun h -> 
      (contains h t)
      ))
    (ensures (fun h0 s h1 -> 
      (contains h0 t)
      ))
let mk_array max t =
  let len = FStar.Array.length t in
  let a = FStar.Array.create len 0 in
  populate_array max t 0 a;
  a
