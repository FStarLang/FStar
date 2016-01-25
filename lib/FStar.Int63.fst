(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)

module FStar.Int63
val min_value_int : int
let min_value_int = -4611686018427387904

val max_value_int : int
let max_value_int = 4611686018427387903

let within_int63 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type int63 =
  | Int63 : i:int{within_int63 i} -> int63

val min_value : int63
let min_value = Int63 min_value_int

val max_value : int63
let max_value = Int63 max_value_int

val as_int: i:int63 -> GTot int
let as_int (Int63 i) = i

type nat63 = x:int63{Prims.op_GreaterThanOrEqual (as_int x) 0}

//a ?+ b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Plus: i:int63
              -> j:int63
              -> Tot (k:int63{within_int63 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (Int63 i) (Int63 j) =
  if within_int63 (i + j)
  then Int63 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:int63
          -> j:int63{within_int63 (as_int i + as_int j)}
          -> Tot int63
let op_Plus (Int63 i) (Int63 j) = Int63 (i + j)

//a ?- b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Subtraction: i:int63
              -> j:int63
              -> Tot (k:int63{within_int63 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (Int63 i) (Int63 j) =
  if within_int63 (i - j)
  then Int63 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:int63
                 -> j:int63{within_int63 (as_int i - as_int j)}
                 -> Tot int63
let op_Subtraction (Int63 i) (Int63 j) = Int63 (i - j)

//a ?* b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Star:
                 i:int63
              -> j:int63
              -> Tot (k:int63{within_int63 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (Int63 i) (Int63 j) =
  if within_int63 (i * j)
  then Int63 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:int63
          -> j:int63{within_int63 (as_int i * as_int j)}
          -> Tot int63
let op_Star (Int63 i) (Int63 j) = Int63 (i * j)

//When the dividend is negative, the semantics is platform dependent
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Slash: i:int63
                           -> j:int63{as_int j <> 0}
                           -> Tot (k:int63{as_int i >= 0 ==> as_int k = as_int i / as_int j})
let op_Question_Slash (Int63 i) (Int63 j) =
  if i < 0
  then magic ()//mark as admit, because we do not specify the overflow semantics
  else Int63 (i / j)

//division does not overflow when the dividend is non-negative
val op_Slash: i:int63{as_int i >= 0}
           -> j:int63{as_int j <> 0}
           -> Tot int63
let op_Slash (Int63 i) (Int63 j) = Int63 (i / j)

//a ?% b can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Percent:
                i:int63
             -> j:int63{as_int j <> 0}
             -> Tot (k:int63{not(as_int i = min_value_int && as_int j = -1)
                             ==> as_int k = as_int i % as_int j})
let op_Question_Percent (Int63 i) (Int63 j) =
  if i=min_value_int && j = -1
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int63 (i % j)

//From: http://stackoverflow.com/questions/19285163/does-modulus-overflow
//Overflow can occur during a modulo operation when the dividend is equal to the
//minimum (negative) value for the signed integer type and the divisor is equal
//to -1.
val op_Percent: i:int63
             -> j:int63{as_int j <> 0 /\ not(i = min_value && as_int j = -1)}
             -> Tot int63
let op_Percent (Int63 i) (Int63 j) = Int63 (i % j)

//?- a    can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Minus: i:int63
                   -> Tot int63
let op_Question_Minus (Int63 i) =
  if i = min_value_int
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int63 (-i)

val op_Minus: i:int63{i <> min_value}
           -> Tot int63
let op_Minus (Int63 i) = Int63 (-i)

val op_Less_Equals: i:int63
                 -> j:int63
                 -> Tot bool
let op_Less_Equals (Int63 i) (Int63 j) = i <= j

val op_Less: i:int63
          -> j:int63
          -> Tot bool
let op_Less (Int63 i) (Int63 j) = i < j

val op_Greater_Equals: i:int63
                    -> j:int63
                    -> Tot bool
let op_Greater_Equals (Int63 i) (Int63 j) = i >= j

val op_Greater: i:int63
             -> j:int63
             -> Tot bool
let op_Greater (Int63 i) (Int63 j) = i > j
