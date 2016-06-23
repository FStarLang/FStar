module FproductLemmas

#reset-options

val auxiliary_lemma_00: a:int -> b:int -> c:int -> Lemma (ensures ((a+b)-c=a+b-c))
let auxiliary_lemma_00 a b c = ()

val auxiliary_lemma_0: a:int -> b:int -> c:int -> Lemma (ensures (a+b-c = a-c+b))
let auxiliary_lemma_0 a b c = ()

val auxiliary_lemma_1: a:int -> b:int -> Lemma (requires (b = 0)) (ensures (a+b=a/\b+a=a))
let auxiliary_lemma_1 a b = ()

val auxiliary_lemma_2: a:nat  -> Lemma (requires (a <> 0)) (ensures (a-1>=0))
let auxiliary_lemma_2 a = ()

val auxiliary_lemma_3: a:nat -> i:nat -> Lemma (a+a*(i-1)=a*i)
let auxiliary_lemma_3 a i = ()

val auxiliary_lemma_4: a:nat -> i:nat -> j:nat -> Lemma (a*i+a*j=(i+j)*a)
let auxiliary_lemma_4 a i j = ()

val auxiliary_lemma_5: a:int -> b:int -> c:int -> Lemma (a*b+c=c+a*b)
let auxiliary_lemma_5 a b c = ()

val auxiliary_lemma_6: a:int -> b:int -> c:int -> d:int -> Lemma (a + b + c + d = c + a + b + d)
let auxiliary_lemma_6 a b c d = ()

val auxiliary_lemma_7: a:nat -> b:nat -> Lemma (requires (a-b <> 0 /\ a >= b)) (ensures (a-1 >=0/\a-1>=b))
let auxiliary_lemma_7 a b = ()

(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_70: a:int -> b:int -> c:int -> Lemma (ensures (a-(b-c)=a-b+c))
let auxiliary_lemma_70 a b c = ()

val auxiliary_lemma_8: a:nat -> b:nat -> Lemma (requires (a-b=0 /\ a>=b)) (ensures (a=b))
let auxiliary_lemma_8 a b = ()

val auxiliary_lemma_01: a:int -> b:int -> Lemma (ensures (a+b = b+a))
let auxiliary_lemma_01 a b = ()

val auxiliary_lemma_02: len:nat -> idx:nat -> Lemma (requires (len=0)) (ensures (len+idx=idx))
let auxiliary_lemma_02 len idx = ()

val auxiliary_lemma_03: x:nat -> Lemma (requires (True)) (ensures (x * 0 = 0))
let auxiliary_lemma_03 x = ()

(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_80: 
  unit -> Lemma (ensures (forall a b. a = 0 ==> (a * b = 0 /\ b * a = 0)))
let auxiliary_lemma_80 () = ()

(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_90 : a:int -> Lemma (ensures (a - a = 0))
let auxiliary_lemma_90 a = ()

val auxiliary_lemma_100: a:int -> b:int -> Lemma
  (requires (b = 0)) (ensures (a * b = 0))
let auxiliary_lemma_100 a b = ()  

(* Helper lemmas that avoid super long computation or intensive use of "cuts" *)
(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_0 : 
  a:int -> b:int -> c:int -> 
  Lemma
    (requires (True))
    (ensures ( a - c - b + c = a - b ))
let helper_lemma_0 a b c = ()

(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_1 : a:int -> Lemma (ensures (1 * a = a))
let helper_lemma_1 a = ()

(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_2 : a:nat -> Lemma (ensures (a + a = 2 * a))
let helper_lemma_2 a = ()
	
(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_3:
	 a:nat -> b:nat -> c:nat -> d:nat ->
	 Lemma
	   (requires ( a <= c /\ b <= d ))
	   (ensures ( a*b <= c*d ))
let helper_lemma_3 a b c d = ()
	
(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_4:
  a:nat -> b:nat -> Lemma (ensures ( a * b >= 0 ))
let helper_lemma_4 a b = ()

val helper_lemma_5: a:nat -> b:nat -> c:nat -> d:nat -> Lemma (a + b * c * d = c * d * b + a)
let helper_lemma_5 a b c d = ()

val helper_lemma_7: norm_length:nat -> ctr:pos{ctr < norm_length} -> 
  Lemma 
    (requires (True))
    (ensures (norm_length - ctr + 1 >= 0 /\ norm_length - ctr + 1 <= norm_length))
    [SMTPat (norm_length - ctr + 1)]
let helper_lemma_7 norm_length ctr = ()

val helper_lemma_8: norm_length:nat -> ctr:nat ->
  Lemma 
    (requires (ctr <= norm_length /\ ctr <> 0))
    (ensures (ctr > 0 /\ norm_length - ctr < norm_length /\ norm_length-ctr+1 = norm_length - (ctr-1)))
let helper_lemma_8 norm_length ctr = ()

val helper_lemma_9: norm_length:nat -> ctr:nat -> 
  Lemma (requires (ctr = 0))
	(ensures (norm_length - ctr = norm_length))
let helper_lemma_9 norm_length ctr = ()	

val helper_lemma_10: x:int -> Lemma (2 * x = x + x)
let helper_lemma_10 x = ()

val helper_lemma_11: size:nat -> norm_length:nat{size - norm_length - 1 >= 0} -> x:nat -> Lemma
  (requires (x = (size - norm_length - 1) / 2))
  (ensures (2 * x < size))
let helper_lemma_11 size norm_length x = ()  

val helper_lemma_12: a:nat -> v:nat -> p:nat -> b:nat -> Lemma (a * v * p + (a * b) = a * (p * v + b))
let helper_lemma_12 a v p b = ()

val helper_lemma_13: a:int -> Lemma (a * 0 = 0 /\ 0 * a = 0)
let helper_lemma_13 a = ()

val auxiliary_lemma_04: a:int -> b:int -> c:int -> Lemma (ensures ((a+b)+c = (a+c)+b))
let auxiliary_lemma_04 a b c = ()

val remove_paren_lemma: a:int -> b:int -> c:int -> Lemma (a + (b + c) = a + b + c /\ (a+b)+c = a+b+c)
let remove_paren_lemma a b c = ()

val factorise_lemma: x:nat -> ctr:nat -> Lemma (ctr * x + x = (ctr+1) * x)
let factorise_lemma x ctr = ()

val ineq_lemma: unit -> Lemma (forall (a:nat) (b':nat) (c:nat) (d:nat). a <= c /\ b' <= d ==> a * b' <= c * d)
let ineq_lemma () = ()

val ineq_lemma_2: a:nat -> b:nat -> c:nat ->
  Lemma (requires (a <= b /\ b < c))
	(ensures (a < c))
let ineq_lemma_2 a b c = ()	

val ineq_lemma_3: a:nat -> b:nat -> c:nat -> 
  Lemma (requires (a < c /\ b < c))
	(ensures (a * b < c * c))
let ineq_lemma_3 a b c = ()	
