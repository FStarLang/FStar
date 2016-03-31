module FStar.UInt64
open FStar.Mul
val min_value_int : int
let min_value_int = 0

val max_value_int : int
let max_value_int = 18446744073709551615

let within_uint64 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type uint64' =
  | UInt64 : i:int{within_uint64 i} -> uint64'

(* abstract *) type uint64 = uint64'

val min_value : uint64
let min_value = UInt64 min_value_int

val max_value : uint64
let max_value = UInt64 max_value_int

val as_int: i:uint64 -> GTot int
let as_int (UInt64 i) = i

//a ?+ b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Plus: i:uint64
              -> j:uint64
              -> Tot (k:uint64{within_uint64 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (UInt64 i) (UInt64 j) =
  if within_uint64 (i + j)
  then UInt64 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:uint64
          -> j:uint64{within_uint64 (as_int i + as_int j)}
          -> Tot uint64
let op_Plus (UInt64 i) (UInt64 j) = UInt64 (i + j)

//a ?- b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Subtraction: i:uint64
              -> j:uint64
              -> Tot (k:uint64{within_uint64 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (UInt64 i) (UInt64 j) =
  if within_uint64 (i - j)
  then UInt64 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:uint64
                 -> j:uint64{within_uint64 (as_int i - as_int j)}
                 -> Tot uint64
let op_Subtraction (UInt64 i) (UInt64 j) = UInt64 (i - j)

//a ?* b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Star:
                 i:uint64
              -> j:uint64
              -> Tot (k:uint64{within_uint64 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (UInt64 i) (UInt64 j) =
  if within_uint64 (i * j)
  then UInt64 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:uint64
          -> j:uint64{within_uint64 (as_int i * as_int j)}
          -> Tot uint64
let op_Star (UInt64 i) (UInt64 j) = UInt64 (i * j)

// division cannot overflow with unsigned integers
val op_Slash: i:uint64
           -> j:uint64{as_int j <> 0}
           -> Tot uint64
let op_Slash (UInt64 i) (UInt64 j) = UInt64 (i / j)

//a ?% b cannot overflow
val op_Percent: i:uint64
             -> j:uint64{as_int j <> 0}
             -> Tot uint64
let op_Percent (UInt64 i) (UInt64 j) = UInt64 (i % j)

val op_Less_Equals: i:uint64
                 -> j:uint64
                 -> Tot bool
let op_Less_Equals (UInt64 i) (UInt64 j) = i <= j

val op_Less: i:uint64
          -> j:uint64
          -> Tot bool
let op_Less (UInt64 i) (UInt64 j) = (i < j)

val op_Greater_Equals: i:uint64
                    -> j:uint64
                    -> Tot bool
let op_Greater_Equals (UInt64 i) (UInt64 j) = i >= j

val op_Greater: i:uint64
             -> j:uint64
             -> Tot bool
let op_Greater (UInt64 i) (UInt64 j) = i > j
