module Bignum.Bigint

open FStar.ST
open FStar.Heap
open FStar.Ghost
open IntLib
open Bignum.Parameters
open SInt
open SBuffer

type template = nat -> Tot pos
type template_const = t:template{ forall (n:nat). t n = t 0 }

val byte_templ: template
let byte_templ = fun x -> 8

type bigint = uint64s //buffer platform_size
type bigint_wide = uint128s //buffer platform_wide
type bytes = uint8s //buffer 8

(* Normalized big integer type *)
abstract let norm (h:heap) (#size:pos) (b:buffer size) : GTot Type0 =
  live h b /\ length b >= norm_length 
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==>  v (get h b i) < pow2 (templ i))

abstract let null (h:heap) (#size:pos) (b:buffer size) : GTot Type0 =
  live h b /\ (forall (n:nat). {:pattern (v (get h b n))} n < length b ==> v (get h b n) = 0)

let filled (h:heap) (#size:pos) (b:buffer size) : GTot Type0 =
  live h b /\ length b >= norm_length /\ 
  (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> (pow2 ndiff' <= v (get h b i) /\ v (get h b i) < pow2 ndiff))

val bitweight : t:template -> n:nat -> GTot nat
let rec bitweight t n = 
  match n with 
  | 0 -> 0
  | _ -> t (n-1) + bitweight t (n-1)

val eval : h:heap -> #size:pos -> b:buffer size{live h b} -> n:nat{n <= length b} -> GTot nat
let rec eval h #size b n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight templ (n-1)) * v (get h b (n-1)) + eval h  b (n-1)

val eval_bytes : h:heap -> b:bytes{live h b} -> n:nat{n <= length b} -> GTot nat
let rec eval_bytes h b n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight byte_templ (n-1)) * v (get h b (n-1)) + eval_bytes h b (n-1)

val maxValue: h:heap -> #size:pos -> b:buffer size{live h  b} -> l:pos{l <= length  b} -> GTot nat
let rec maxValue h #size b l = 
  match l with
  | 1 -> v (get h  b 0)
  | _ -> if maxValue h  b (l-1) > v (get h  b (l-1)) then maxValue h  b (l-1)
	 else v (get h  b (l-1))

val maxValue_lemma_aux: h:heap -> #size:pos -> b:buffer size{live h b} -> l:pos{l<=length b} ->
  Lemma (forall (i:nat). i < l ==> v (get h b i) <= maxValue h b l)
let rec maxValue_lemma_aux h #size b l = match l with | 1 -> () | _ -> maxValue_lemma_aux h b (l-1)

val maxValue_lemma: h:heap -> #size:pos -> b:buffer size{live h b /\ length b > 0} ->
  Lemma (requires (True)) 
	(ensures (forall (i:nat). {:pattern (v (get h b i))} i < length b ==> v (get h b i) <= maxValue h b (length b)))
let rec maxValue_lemma h #size b = maxValue_lemma_aux h b (length b)

val maxValue_bound_lemma_aux: h:heap -> #size:pos -> b:buffer size{live h b /\ length b > 0} -> l:pos{l<=length b} -> 
  bound:nat ->  Lemma (requires (forall (i:nat). i < l ==> v (get h b i) <= bound))
	             (ensures (maxValue h b l <= bound))
let rec maxValue_bound_lemma_aux h #size b l bound = match l with | 1 -> () | _ -> maxValue_bound_lemma_aux h b (l-1) bound

val maxValue_bound_lemma: h:heap -> #size:pos -> b:buffer size{live h b /\ length b > 0} -> bound:nat ->  
  Lemma (requires (forall (i:nat). i < length b ==> v (get h b i) <= bound))
	      (ensures (maxValue h b (length b) <= bound))
let maxValue_bound_lemma h #size b bound = maxValue_bound_lemma_aux h b (length b) bound

val maxValueNorm: h:heap -> #size:pos -> b:buffer size{live h  b /\ length  b >= norm_length} -> GTot nat
let maxValueNorm h #size b = maxValue h b norm_length

val maxValueIdx: h:heap -> #size:pos -> b:buffer size{live h  b} -> l:pos{l<=length  b} -> GTot nat
let rec maxValueIdx h #size b l = 
  match l with 
  | 1 -> 0
  | _ -> if maxValue h  b l = v (get h b (l-1)) then l - 1 else maxValueIdx h b (l-1)

val maxValue_eq_lemma: 
  ha:heap -> hb:heap -> #size:pos -> a:buffer size{live ha  a} -> b:buffer size{live hb  b} -> l:nat -> Lemma 
    (requires (equal ha a hb b /\ l > 0 /\ l <= length a)) 
    (ensures (equal ha a hb b /\ l > 0 /\ l <= length a /\ maxValue ha a l = maxValue hb b l))
let rec maxValue_eq_lemma ha hb #size a b l = 
  match l with
  | 1 -> ()
  | _ -> cut (forall (i:nat). i < length b ==> v (get ha a i) = v (get hb b i)); 
         maxValue_eq_lemma ha hb a b (l-1)
  
val maxValueNorm_eq_lemma: 
  ha:heap -> hb:heap -> #size:pos -> a:buffer size{ live ha a /\ length a >= norm_length } -> b:buffer size{ live hb b /\ length b >= norm_length } -> 
  Lemma 
    (requires (equal ha a hb b)) 
    (ensures (maxValueNorm ha a = maxValueNorm hb b))
let maxValueNorm_eq_lemma ha hb #size a b = maxValue_eq_lemma ha hb a b norm_length

val eval_eq_lemma: ha:heap -> hb:heap -> #size_a:pos -> a:buffer size_a{live ha a} -> #size_b:pos -> b:buffer size_b{live hb b} ->
  len:nat{ (len <= length a) /\ (len <= length b) } -> Lemma
    (requires ( (forall (i:nat). i < len ==> v (get ha a i) = v (get hb b i)) ))
    (ensures ( eval ha a len = eval hb b len ))
let rec eval_eq_lemma ha hb #size_a a #size_b b len =
  match len with
  | 0 -> ()
  | _ -> eval_eq_lemma ha hb a b (len-1)

#reset-options "--z3timeout 20"

val eval_partial_eq_lemma: ha:heap -> hb:heap -> #size:pos -> a:buffer size{live ha a} -> b:buffer size{live hb b} -> 
  ctr:nat -> len:nat{ ctr <= len /\ len <= length a /\ len <= length b} -> Lemma
    (requires (equalSub ha a ctr hb b ctr (len-ctr)))
    (ensures ( eval ha a len - eval ha a ctr = eval hb b len - eval hb b ctr ))
let rec eval_partial_eq_lemma ha hb #size a b ctr len =
  match len-ctr with
  | 0 -> ()
  | _ -> 
    cut (forall (i:nat). {:pattern (v (get ha a i))} i < len - ctr ==> v (get ha a (ctr+i)) = v (get hb b (ctr+i))); 
    eval_partial_eq_lemma ha hb a b ctr (len-1); 
    cut (eval ha a (len-1) - eval ha a ctr = eval hb b (len-1) - eval hb b ctr); 
    cut (eval ha a len = pow2 (bitweight templ (len-1)) * v (get ha a (len-1)) + eval ha a (len-1) /\ eval hb b len = pow2 (bitweight templ (len-1)) * v (get hb b (len-1)) + eval hb b (len-1)); 
    cut (v (get ha a (ctr + (len-ctr-1))) = v (get hb b (len-1)))

#reset-options

val eval_null: h:heap -> #size:pos -> b:buffer size{live h b} -> len:nat{len <= length b} -> Lemma
    (requires (forall (i:nat). {:pattern (v (get h b i))} i < len ==> v (get h b i) = 0))
    (ensures (eval h b len = 0))
let rec eval_null h #size b len =
  match len with
  | 0 -> ()
  | _ -> eval_null h b (len-1)

val max_value_of_null_lemma: h:heap -> #size:pos -> b:buffer size{live h b /\ length b > 0} -> l:pos{l <= length b} ->
  Lemma (requires (null h b))
	(ensures (maxValue h b l = 0))
let rec max_value_of_null_lemma h #size b l = 
  match l with
  | 1 -> ()
  | _ -> max_value_of_null_lemma h b (l-1)

val distributivity_add_right: a:int -> b:int -> c:int -> Lemma (a*(b+c) = a * b + a * c)
let distributivity_add_right a b c = ()
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma ((a+b)*c = a * c + b * c)
let distributivity_add_left a b c = ()
val distributivity_sub_right: a:int -> b:int -> c:int -> Lemma (a*(b-c) = a * b - a * c)
let distributivity_sub_right a b c = ()
val distributivity_sub_left: a:int -> b:int -> c:int -> Lemma ((a-b)*c = a * c - b * c)
let distributivity_sub_left a b c = ()
val paren_mul_left: a:int -> b:int -> c:int -> Lemma (a * b * c = ( a * b ) * c)
let paren_mul_left a b c = ()
val paren_mul_right: a:int -> b:int -> c:int -> Lemma (a * b * c = a * (b * c))
let paren_mul_right a b c = ()
val paren_add_left: a:int -> b:int -> c:int -> Lemma (a + b + c = ( a + b ) + c)
let paren_add_left a b c = ()
val paren_add_right: a:int -> b:int -> c:int -> Lemma (a + b + c = a + (b + c))
let paren_add_right a b c = ()

let live (h:heap) (#size:pos) (b:buffer size) : GTot Type0 = live h b /\ length b >= norm_length
