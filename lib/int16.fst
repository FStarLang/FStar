(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)

module FStar.Int16
val min_value_int : int
let min_value_int = -32768

val max_value_int : int
let max_value_int = 32767

let within_int16 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type int16 =
  | Int16 : i:int{within_int16 i} -> int16

val min_value : int16
let min_value = Int16 min_value_int

val max_value : int16
let max_value = Int16 max_value_int

val as_int: i:int16 -> GTot int
let as_int (Int16 i) = i

type nat16 = x:int16{Prims.op_GreaterThanOrEqual (as_int x) 0}

//a ?+ b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Plus: i:int16
              -> j:int16
              -> Tot (k:int16{within_int16 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (Int16 i) (Int16 j) =
  if within_int16 (i + j)
  then Int16 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:int16
          -> j:int16{within_int16 (as_int i + as_int j)}
          -> Tot int16
let op_Plus (Int16 i) (Int16 j) = Int16 (i + j)

//a ?- b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Subtraction: i:int16
              -> j:int16
              -> Tot (k:int16{within_int16 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (Int16 i) (Int16 j) =
  if within_int16 (i - j)
  then Int16 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:int16
                 -> j:int16{within_int16 (as_int i - as_int j)}
                 -> Tot int16
let op_Subtraction (Int16 i) (Int16 j) = Int16 (i - j)

//a ?* b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Star:
                 i:int16
              -> j:int16
              -> Tot (k:int16{within_int16 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (Int16 i) (Int16 j) =
  if within_int16 (i * j)
  then Int16 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:int16
          -> j:int16{within_int16 (as_int i * as_int j)}
          -> Tot int16
let op_Star (Int16 i) (Int16 j) = Int16 (i * j)

//When the dividend is negative, the semantics is platform dependent
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Slash: i:int16
                           -> j:int16{as_int j <> 0}
                           -> Tot (k:int16{as_int i >= 0 ==> as_int k = as_int i / as_int j})
let op_Question_Slash (Int16 i) (Int16 j) =
  if i < 0
  then magic ()//mark as admit, because we do not specify the overflow semantics
  else Int16 (i / j)

//division does not overflow when the dividend is non-negative
val op_Slash: i:int16{as_int i >= 0}
           -> j:int16{as_int j <> 0}
           -> Tot int16
let op_Slash (Int16 i) (Int16 j) = Int16 (i / j)

//a ?% b can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Percent:
                i:int16
             -> j:int16{as_int j <> 0}
             -> Tot (k:int16{not(as_int i = min_value_int && as_int j = -1)
                             ==> as_int k = as_int i % as_int j})
let op_Question_Percent (Int16 i) (Int16 j) =
  if i=min_value_int && j = -1
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int16 (i % j)

//From: http://stackoverflow.com/questions/19285163/does-modulus-overflow
//Overflow can occur during a modulo operation when the dividend is equal to the
//minimum (negative) value for the signed integer type and the divisor is equal
//to -1.
val op_Percent: i:int16
             -> j:int16{as_int j <> 0 /\ not(i = min_value && as_int j = -1)}
             -> Tot int16
let op_Percent (Int16 i) (Int16 j) = Int16 (i % j)

//?- a    can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Minus: i:int16
                   -> Tot int16
let op_Question_Minus (Int16 i) =
  if i = min_value_int
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int16 (-i)

val op_Minus: i:int16{i <> min_value}
           -> Tot int16
let op_Minus (Int16 i) = Int16 (-i)

val op_Less_Equals: i:int16
                 -> j:int16
                 -> Tot bool
let op_Less_Equals (Int16 i) (Int16 j) = i <= j

val op_Less: i:int16
          -> j:int16
          -> Tot bool
let op_Less (Int16 i) (Int16 j) = i < j

val op_Greater_Equals: i:int16
                    -> j:int16
                    -> Tot bool
let op_Greater_Equals (Int16 i) (Int16 j) = i >= j

val op_Greater: i:int16
             -> j:int16
             -> Tot bool
let op_Greater (Int16 i) (Int16 j) = i > j
