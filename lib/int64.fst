(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)

module FStar.Int64
val min_value_int : int
let min_value_int = -9223372036854775808

val max_value_int : int
let max_value_int = 9223372036854775807

let within_int64 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type int64 =
  | Int64 : i:int{within_int64 i} -> int64

val min_value : int64
let min_value = Int64 min_value_int

val max_value : int64
let max_value = Int64 max_value_int

val as_int: i:int64 -> GTot int
let as_int (Int64 i) = i

type nat64 = x:int64{Prims.op_GreaterThanOrEqual (as_int x) 0}

//a ?+ b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Plus: i:int64
              -> j:int64
              -> Tot (k:int64{within_int64 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (Int64 i) (Int64 j) =
  if within_int64 (i + j)
  then Int64 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:int64
          -> j:int64{within_int64 (as_int i + as_int j)}
          -> Tot int64
let op_Plus (Int64 i) (Int64 j) = Int64 (i + j)

//a ?- b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Subtraction: i:int64
              -> j:int64
              -> Tot (k:int64{within_int64 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (Int64 i) (Int64 j) =
  if within_int64 (i - j)
  then Int64 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:int64
                 -> j:int64{within_int64 (as_int i - as_int j)}
                 -> Tot int64
let op_Subtraction (Int64 i) (Int64 j) = Int64 (i - j)

//a ?* b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Star:
                 i:int64
              -> j:int64
              -> Tot (k:int64{within_int64 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (Int64 i) (Int64 j) =
  if within_int64 (i * j)
  then Int64 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:int64
          -> j:int64{within_int64 (as_int i * as_int j)}
          -> Tot int64
let op_Star (Int64 i) (Int64 j) = Int64 (i * j)

//When the dividend is negative, the semantics is platform dependent
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Slash: i:int64
                           -> j:int64{as_int j <> 0}
                           -> Tot (k:int64{as_int i >= 0 ==> as_int k = as_int i / as_int j})
let op_Question_Slash (Int64 i) (Int64 j) =
  if i < 0
  then magic ()//mark as admit, because we do not specify the overflow semantics
  else Int64 (i / j)

//division does not overflow when the dividend is non-negative
val op_Slash: i:int64{as_int i >= 0}
           -> j:int64{as_int j <> 0}
           -> Tot int64
let op_Slash (Int64 i) (Int64 j) = Int64 (i / j)

//a ?% b can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Percent:
                i:int64
             -> j:int64{as_int j <> 0}
             -> Tot (k:int64{not(as_int i = min_value_int && as_int j = -1)
                             ==> as_int k = as_int i % as_int j})
let op_Question_Percent (Int64 i) (Int64 j) =
  if i=min_value_int && j = -1
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int64 (i % j)

//From: http://stackoverflow.com/questions/19285163/does-modulus-overflow
//Overflow can occur during a modulo operation when the dividend is equal to the
//minimum (negative) value for the signed integer type and the divisor is equal
//to -1.
val op_Percent: i:int64
             -> j:int64{as_int j <> 0 /\ not(i = min_value && as_int j = -1)}
             -> Tot int64
let op_Percent (Int64 i) (Int64 j) = Int64 (i % j)

//?- a    can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Minus: i:int64
                   -> Tot int64
let op_Question_Minus (Int64 i) =
  if i = min_value_int
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int64 (-i)

val op_Minus: i:int64{i <> min_value}
           -> Tot int64
let op_Minus (Int64 i) = Int64 (-i)

val op_Less_Equals: i:int64
                 -> j:int64
                 -> Tot bool
let op_Less_Equals (Int64 i) (Int64 j) = i <= j

val op_Less: i:int64
          -> j:int64
          -> Tot bool
let op_Less (Int64 i) (Int64 j) = i < j

val op_Greater_Equals: i:int64
                    -> j:int64
                    -> Tot bool
let op_Greater_Equals (Int64 i) (Int64 j) = i >= j

val op_Greater: i:int64
             -> j:int64
             -> Tot bool
let op_Greater (Int64 i) (Int64 j) = i > j
