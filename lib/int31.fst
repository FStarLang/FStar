(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)

module FStar.Int31
val min_value_int : int
let min_value_int = -1073741824

val max_value_int : int
let max_value_int = 1073741823

let within_int31 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type int31 =
  | Int31 : i:int{within_int31 i} -> int31

val min_value : int31
let min_value = Int31 min_value_int

val max_value : int31
let max_value = Int31 max_value_int

val as_int: i:int31 -> GTot int
let as_int (Int31 i) = i

type nat31 = x:int31{Prims.op_GreaterThanOrEqual (as_int x) 0}

//a ?+ b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Plus: i:int31
              -> j:int31
              -> Tot (k:int31{within_int31 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (Int31 i) (Int31 j) =
  if within_int31 (i + j)
  then Int31 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:int31
          -> j:int31{within_int31 (as_int i + as_int j)}
          -> Tot int31
let op_Plus (Int31 i) (Int31 j) = Int31 (i + j)

//a ?- b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Subtraction: i:int31
              -> j:int31
              -> Tot (k:int31{within_int31 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (Int31 i) (Int31 j) =
  if within_int31 (i - j)
  then Int31 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:int31
                 -> j:int31{within_int31 (as_int i - as_int j)}
                 -> Tot int31
let op_Subtraction (Int31 i) (Int31 j) = Int31 (i - j)

//a ?* b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Star:
                 i:int31
              -> j:int31
              -> Tot (k:int31{within_int31 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (Int31 i) (Int31 j) =
  if within_int31 (i * j)
  then Int31 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:int31
          -> j:int31{within_int31 (as_int i * as_int j)}
          -> Tot int31
let op_Star (Int31 i) (Int31 j) = Int31 (i * j)

//When the dividend is negative, the semantics is platform dependent
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Slash: i:int31
                           -> j:int31{as_int j <> 0}
                           -> Tot (k:int31{as_int i >= 0 ==> as_int k = as_int i / as_int j})
let op_Question_Slash (Int31 i) (Int31 j) =
  if i < 0
  then magic ()//mark as admit, because we do not specify the overflow semantics
  else Int31 (i / j)

//division does not overflow when the dividend is non-negative
val op_Slash: i:int31{as_int i >= 0}
           -> j:int31{as_int j <> 0}
           -> Tot int31
let op_Slash (Int31 i) (Int31 j) = Int31 (i / j)

//a ?% b can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Percent:
                i:int31
             -> j:int31{as_int j <> 0}
             -> Tot (k:int31{not(as_int i = min_value_int && as_int j = -1)
                             ==> as_int k = as_int i % as_int j})
let op_Question_Percent (Int31 i) (Int31 j) =
  if i=min_value_int && j = -1
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int31 (i % j)

//From: http://stackoverflow.com/questions/19285163/does-modulus-overflow
//Overflow can occur during a modulo operation when the dividend is equal to the
//minimum (negative) value for the signed integer type and the divisor is equal
//to -1.
val op_Percent: i:int31
             -> j:int31{as_int j <> 0 /\ not(i = min_value && as_int j = -1)}
             -> Tot int31
let op_Percent (Int31 i) (Int31 j) = Int31 (i % j)

//?- a    can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Minus: i:int31
                   -> Tot int31
let op_Question_Minus (Int31 i) =
  if i = min_value_int
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int31 (-i)

val op_Minus: i:int31{i <> min_value}
           -> Tot int31
let op_Minus (Int31 i) = Int31 (-i)

val op_Less_Equals: i:int31
                 -> j:int31
                 -> Tot bool
let op_Less_Equals (Int31 i) (Int31 j) = i <= j

val op_Less: i:int31
          -> j:int31
          -> Tot bool
let op_Less (Int31 i) (Int31 j) = i < j

val op_Greater_Equals: i:int31
                    -> j:int31
                    -> Tot bool
let op_Greater_Equals (Int31 i) (Int31 j) = i >= j

val op_Greater: i:int31
             -> j:int31
             -> Tot bool
let op_Greater (Int31 i) (Int31 j) = i > j
