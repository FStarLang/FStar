(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: set.fsi heap.fst st.fst all.fst
  --*)

module FStar.Int8
val min_value_int : int
let min_value_int = -128

val max_value_int : int
let max_value_int = 127

let within_int8 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type int8 =
  | Int8 : i:int{within_int8 i} -> int8

val min_value : int8
let min_value = Int8 min_value_int

val max_value : int8
let max_value = Int8 max_value_int

val as_int: i:int8 -> GTot int
let as_int (Int8 i) = i

type nat8 = x:int8{Prims.op_GreaterThanOrEqual (as_int x) 0}

//a ?+ b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Plus: i:int8
              -> j:int8
              -> Tot (k:int8{within_int8 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (Int8 i) (Int8 j) =
  if within_int8 (i + j)
  then Int8 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:int8
          -> j:int8{within_int8 (as_int i + as_int j)}
          -> Tot int8
let op_Plus (Int8 i) (Int8 j) = Int8 (i + j)

//a ?- b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Subtraction: i:int8
              -> j:int8
              -> Tot (k:int8{within_int8 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (Int8 i) (Int8 j) =
  if within_int8 (i - j)
  then Int8 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:int8
                 -> j:int8{within_int8 (as_int i - as_int j)}
                 -> Tot int8
let op_Subtraction (Int8 i) (Int8 j) = Int8 (i - j)

//a ?* b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Star:
                 i:int8
              -> j:int8
              -> Tot (k:int8{within_int8 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (Int8 i) (Int8 j) =
  if within_int8 (i * j)
  then Int8 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:int8
          -> j:int8{within_int8 (as_int i * as_int j)}
          -> Tot int8
let op_Star (Int8 i) (Int8 j) = Int8 (i * j)

//When the dividend is negative, the semantics is platform dependent
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Slash: i:int8
                           -> j:int8{as_int j <> 0}
                           -> Tot (k:int8{as_int i >= 0 ==> as_int k = as_int i / as_int j})
let op_Question_Slash (Int8 i) (Int8 j) =
  if i < 0
  then magic ()//mark as admit, because we do not specify the overflow semantics
  else Int8 (i / j)

//division does not overflow when the dividend is non-negative
val op_Slash: i:int8{as_int i >= 0}
           -> j:int8{as_int j <> 0}
           -> Tot int8
let op_Slash (Int8 i) (Int8 j) = Int8 (i / j)

//a ?% b can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Percent:
                i:int8
             -> j:int8{as_int j <> 0}
             -> Tot (k:int8{not(as_int i = min_value_int && as_int j = -1)
                             ==> as_int k = as_int i % as_int j})
let op_Question_Percent (Int8 i) (Int8 j) =
  if i=min_value_int && j = -1
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int8 (i % j)

//From: http://stackoverflow.com/questions/19285163/does-modulus-overflow
//Overflow can occur during a modulo operation when the dividend is equal to the
//minimum (negative) value for the signed integer type and the divisor is equal
//to -1.
val op_Percent: i:int8
             -> j:int8{as_int j <> 0 /\ not(i = min_value && as_int j = -1)}
             -> Tot int8
let op_Percent (Int8 i) (Int8 j) = Int8 (i % j)

//?- a    can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Minus: i:int8
                   -> Tot int8
let op_Question_Minus (Int8 i) =
  if i = min_value_int
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int8 (-i)

val op_Minus: i:int8{i <> min_value}
           -> Tot int8
let op_Minus (Int8 i) = Int8 (-i)

val op_Less_Equals: i:int8
                 -> j:int8
                 -> Tot bool
let op_Less_Equals (Int8 i) (Int8 j) = i <= j

val op_Less: i:int8
          -> j:int8
          -> Tot bool
let op_Less (Int8 i) (Int8 j) = i < j

val op_Greater_Equals: i:int8
                    -> j:int8
                    -> Tot bool
let op_Greater_Equals (Int8 i) (Int8 j) = i >= j

val op_Greater: i:int8
             -> j:int8
             -> Tot bool
let op_Greater (Int8 i) (Int8 j) = i > j
