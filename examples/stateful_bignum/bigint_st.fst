module Bigint

open IntLib
open Limb
open Seq
open SeqProperties
open ST
open Heap
open Array

(* TODO : stabilize the type definitions *)
(* Int types *)
type int64 = int
type integer = int
type u8 = int

let ocaml63 = 63

(* Maps the index of the integer data to the theoretic bit size of the cell *)
type template = nat -> Tot nat
type template_const = t:template{ forall (n:nat). t n = t 0 }

(* Sized integer *)
type tint (max:nat) = (size:nat{ size < max } & content:int{ Bitsize content size })

(* Sized ST array *)
type tarray (max:nat) = array (tint max)

(* Big integer type *)
type bigint = 
  | Bigint63 : data:tarray ocaml63 -> t:template -> bigint

val wordSize: bigint -> Tot pos
let wordSize b = 
  match b with
    | Bigint63 _ _ -> ocaml63

type SameFormat (ha:heap) (hb:heap) (a:bigint) (b:bigint) = 
  (contains ha (Bigint63.data a) /\ contains hb (Bigint63.data b))
  /\ (Bigint63.t a = Bigint63.t b) 
  /\ (Seq.length (sel ha (Bigint63.data a)) = Seq.length (sel hb (Bigint63.data b)))

logic type inHeap (h:heap) (b:bigint) = b2t (contains h (Bigint63.data b))

(* Getters *)

(* Logical only *)
assume logic val getLength : 
	       h:heap -> b:bigint{ inHeap h b } -> 
	       Tot (len:nat{ len = Seq.length (sel h (Bigint63.data b)) })

assume logic val getSize : 
	       h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } -> 
	       Tot (s:nat{s = dfst (Seq.index (sel h (Bigint63.data b)) i) /\  s < (wordSize b)})

assume logic val getValue :
	       h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } ->
	       Tot (v:int{ v = dsnd (Seq.index (sel h (Bigint63.data b)) i)})

assume logic val getContent :
	       h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } ->
	       Tot (v:tint (wordSize b){ v = (Seq.index (sel h (Bigint63.data b)) i)})

val size_of_value_lemma:
  h:heap -> b:bigint{ inHeap h b } -> i:nat{ i < getLength h b } -> 
  Lemma
    (requires (True))
    (ensures (Bitsize (getValue h b i) (getSize h b i)))
let size_of_value_lemma h b i = 
  erase (
      let v = getContent h b i in
      assert ( v = (Seq.index (sel h (Bigint63.data b)) i) /\ True);
      assert ( dfst v = dfst (Seq.index (sel h (Bigint63.data b)) i) /\ True);
      ()
    )

(* Concrete getters *)
val get_content: 
  b:bigint -> i:nat ->
  ST (tint (wordSize b))
     (requires (fun h -> (inHeap h b)
			 /\ (i < getLength h b)))
     (ensures (fun h0 v h1 -> (inHeap h1 b)
			      /\ (modifies !{} h0 h1)
			      /\ (i < getLength h1 b)
			      /\ (v = getContent h1 b i)))
let get_content b i =
  match b with 
  | Bigint63 data t ->
     Array.index data i

val get_length:
  b:bigint ->
  ST nat
     (requires (fun h -> (inHeap h b)))
     (ensures (fun h0 l h1 -> (h0 == h1) 
			      /\ (inHeap h0 b)
			      /\ (l = getLength h0 b)))
let get_length b =
  match b with
  | Bigint63 data t -> Array.length data		 

val get: 
  b:bigint -> n:nat -> 
  ST int
     (requires (fun h -> inHeap h b /\ n < getLength h b))
     (ensures (fun h0 v h1 -> (modifies !{} h0 h1)
			      /\ (inHeap h1 b)
			      /\ (n < getLength h1 b)
			      /\ (v = getValue h1 b n /\ Bitsize v (getSize h1 b n))))
let get b n =
  match b with
  | Bigint63 data t ->
     let (|size,v|) = (Array.index data n) in v

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
	       (contains h0 (Bigint63.data b))
	       /\ (contains h1 (Bigint63.data b))
	       /\ (idx < Seq.length (sel h0 (Bigint63.data b)))
	       /\ (h1 == Heap.upd h0 (Bigint63.data b) (Seq.upd (sel h0 (Bigint63.data b)) idx v))

	      ))
let updateBigint b idx v =
  match b with
  | Bigint63 data _ ->
     Array.upd data idx v

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
  /\ (Bigint63.t a = getTemplate b)

val copy:
  a:bigint ->
  ST bigint
     (requires (fun h -> inHeap h a /\ getLength h a > 0))
     (ensures (fun h0 b h1 ->
	       (EqualBigint a b h0 h1)
	       /\ (modifies !{} h0 h1)
     ))
let copy a =
  Bigint63 (Array.copy (Bigint63.data a)) (Bigint63.t a)

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

let zero_bigint =
  Bigint63 (Array.create 1 zero_tint) (fun x -> ocaml63)

let one_bigint =
  Bigint63 (Array.create 1 one_tint) (fun x -> ocaml63)

let mk_zero_bigint size template =
  Bigint63 (Array.create size zero_tint) template

let mk_one_bigint size template =
  let one = Bigint63 (Array.create size zero_tint) template in
  updateBigint one 0 one_tint;
  one

val mk_tint: a:bigint -> size:nat{ size < wordSize a } -> value:int{ Bitsize value size } -> 
	     Tot (z:tint (wordSize a))
let mk_tint a size value =
  match a with
  | Bigint63 _ _ -> 
     (|size, value|)

(* Pool of free arrays for temporary computation *)
type array_pool = { free_arrays: ref (list (tarray ocaml63));
	      array_size: ref pos;
	      pool_size: ref nat }

val pool: array_pool
let pool = { free_arrays = ref [];
	     array_size = ref 1;
	     pool_size = ref 0; }

//val initialize_pool: max:nat -> array_size:pos -> ST unit
let initialize_pool max size =
  match max with
  | 0 ->
     pool.array_size := size;
     pool.pool_size := max
  | _ ->
     pool.free_arrays := (Array.create size zero_tint)::!(pool.free_arrays)

val get_from_pool : size:nat -> ST (tarray ocaml63)
				   (requires (fun h -> True))
				   (ensures (fun h0 t h1 -> 
					     (True)))
let get_from_pool size =
  match !(pool.free_arrays), size with
  | hd::tl, _ -> 
     if size = !pool.array_size then
       (pool.free_arrays := tl;
	hd)
     else 
       (
	 (* Issue warning *)
	 (* Create pool mapping size to fresh array of that size ? *)
	 Array.create size zero_tint
       )
  | _, _ -> 
     (* Issue warning *)
     (* Increase pool size *)
     Array.create size zero_tint		 

val return_to_pool : tarray ocaml63 -> ST unit
				     (requires (fun h -> True ))
				     (ensures (fun h0 u h1 -> True))
let return_to_pool a =
  pool.free_arrays := a::!(pool.free_arrays)
