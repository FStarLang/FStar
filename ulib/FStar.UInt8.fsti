module FStar.UInt8
open FStar.Mul
val min_value_int : int
let min_value_int = 0

val max_value_int : int
let max_value_int = 255

let within_uint8 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type uint8' =
  | UInt8 : i:int{within_uint8 i} -> uint8'

abstract type uint8 = uint8'

val min_value : uint8
let min_value = UInt8 min_value_int

val max_value : uint8
let max_value = UInt8 max_value_int

val as_int: i:uint8 -> GTot int
let as_int (UInt8 i) = i

//a ?+ b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Plus: i:uint8
              -> j:uint8
              -> Tot (k:uint8{within_uint8 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (UInt8 i) (UInt8 j) =
  if within_uint8 (i + j)
  then UInt8 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:uint8
          -> j:uint8{within_uint8 (as_int i + as_int j)}
          -> Tot uint8
let op_Plus (UInt8 i) (UInt8 j) = UInt8 (i + j)

//a ?- b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Subtraction: i:uint8
              -> j:uint8
              -> Tot (k:uint8{within_uint8 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (UInt8 i) (UInt8 j) =
  if within_uint8 (i - j)
  then UInt8 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:uint8
                 -> j:uint8{within_uint8 (as_int i - as_int j)}
                 -> Tot uint8
let op_Subtraction (UInt8 i) (UInt8 j) = UInt8 (i - j)

//a ?* b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Star:
                 i:uint8
              -> j:uint8
              -> Tot (k:uint8{within_uint8 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (UInt8 i) (UInt8 j) =
  if within_uint8 (i * j)
  then UInt8 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:uint8
          -> j:uint8{within_uint8 (as_int i * as_int j)}
          -> Tot uint8
let op_Star (UInt8 i) (UInt8 j) = UInt8 (i * j)

// division cannot overflow with unsigned integers
val op_Slash: i:uint8
           -> j:uint8{as_int j <> 0}
           -> Tot uint8
let op_Slash (UInt8 i) (UInt8 j) = UInt8 (i / j)

//a ?% b cannot overflow
val op_Percent: i:uint8
             -> j:uint8{as_int j <> 0}
             -> Tot uint8
let op_Percent (UInt8 i) (UInt8 j) = UInt8 (i % j)

val op_Less_Equals: i:uint8
                 -> j:uint8
                 -> Tot bool
let op_Less_Equals (UInt8 i) (UInt8 j) = i <= j

val op_Less: i:uint8
          -> j:uint8
          -> Tot bool
let op_Less (UInt8 i) (UInt8 j) = (i < j)

val op_Greater_Equals: i:uint8
                    -> j:uint8
                    -> Tot bool
let op_Greater_Equals (UInt8 i) (UInt8 j) = i >= j

val op_Greater: i:uint8
             -> j:uint8
             -> Tot bool
let op_Greater (UInt8 i) (UInt8 j) = i > j
