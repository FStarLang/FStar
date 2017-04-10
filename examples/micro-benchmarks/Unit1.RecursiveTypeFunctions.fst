module Unit1.RecursiveTypeFunctions
//This example is inspired by the use of the id-type in mitls-fstar

type pre_t : Type0 = //the : Type0 annotations are necessary to workaround a mutual induction universe generalization bug
  | T    : nat -> pre_t
  | TofS : pre_s -> pre_t
and pre_s : Type0 = 
  | S    : nat -> pre_s
  | SofT : pre_t -> pre_s

assume type witnessed_nat : nat -> Type0
//Next, we define a recursive type function to carve out a good subset of pre_t, pre_s
val good_t : p:pre_t -> GTot Type0
val good_s:  s:pre_s -> GTot Type0
let rec good_t p = match p with
  | T n    -> witnessed_nat n /\ n >= 17 //explicitly adding the witnessed_nat to force this to be a recursive function in Type, rather than bool
  | TofS s -> good_s s
and good_s s = match s with 
  | S n -> witnessed_nat n /\ n >= 42
  | SofT t -> good_t t

//For the rest of the development, we restrict our attention 
//to just the good subset of pre_t and pre_s
let t = p:pre_t{good_t p}
let s = s:pre_s{good_s s}

//We can now write functions over t and s as usual
val extract_nat_t: x:t -> Tot (n:nat{n >= 17 /\ witnessed_nat n})
val extract_nat_s: x:s -> Tot (n:nat{n >= 17 /\ witnessed_nat n}) 
let rec extract_nat_t x = match x with 
  | T n -> n
  | TofS s -> extract_nat_s s
and extract_nat_s x = match x with 
  | S n -> n
  | SofT t -> extract_nat_t t

//Another example
open FStar.List.Tot
val pointwise_eq : #a:Type -> list a -> list a -> Type0
let rec pointwise_eq #a l1 l2 = 
  match l1, l2 with 
  | [], [] -> True
  | [], _
  | _, [] -> False
  | hd_1::tl_1, hd_2::tl_2 -> hd_1 == hd_2 /\ pointwise_eq tl_1 tl_2

let rec pointwise_eq_length (#a:Type) (l_1:list a) (l_2:list a) 
  : Lemma (requires (pointwise_eq l_1 l_2))
	  (ensures (length l_1 = length l_2))
  = match l_1, l_2 with 
    | [], [] -> ()
    | [], _
    | _, [] -> ()
    | _::tl_1, _::tl_2 -> pointwise_eq_length tl_1 tl_2
    

