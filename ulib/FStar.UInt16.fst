module FStar.UInt16
open FStar.Mul
val min_value_int : int
let min_value_int = 0

val max_value_int : int
let max_value_int = 65535

let within_uint16 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type uint16' =
  | UInt16 : i:int{within_uint16 i} -> uint16'

abstract type uint16 = uint16'

val min_value : uint16
let min_value = UInt16 min_value_int

val max_value : uint16
let max_value = UInt16 max_value_int

val as_int: i:uint16 -> GTot int
let as_int (UInt16 i) = i

//a ?+ b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Plus: i:uint16
              -> j:uint16
              -> Tot (k:uint16{within_uint16 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (UInt16 i) (UInt16 j) =
  if within_uint16 (i + j)
  then UInt16 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:uint16
          -> j:uint16{within_uint16 (as_int i + as_int j)}
          -> Tot uint16
let op_Plus (UInt16 i) (UInt16 j) = UInt16 (i + j)

//a ?- b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Subtraction: i:uint16
              -> j:uint16
              -> Tot (k:uint16{within_uint16 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (UInt16 i) (UInt16 j) =
  if within_uint16 (i - j)
  then UInt16 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:uint16
                 -> j:uint16{within_uint16 (as_int i - as_int j)}
                 -> Tot uint16
let op_Subtraction (UInt16 i) (UInt16 j) = UInt16 (i - j)

//a ?* b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Star:
                 i:uint16
              -> j:uint16
              -> Tot (k:uint16{within_uint16 (op_Multiply (as_int i) (as_int j)) ==> as_int k = op_Multiply (as_int i) (as_int j)})
let op_Question_Star (UInt16 i) (UInt16 j) =
  if within_uint16 (op_Multiply i j)
  then UInt16 (op_Multiply i j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:uint16
          -> j:uint16{within_uint16 (op_Multiply (as_int i) (as_int j))}
          -> Tot uint16
let op_Star (UInt16 i) (UInt16 j) = UInt16 (op_Multiply i j)

// division cannot overflow with unsigned integers
val op_Slash: i:uint16
           -> j:uint16{as_int j <> 0}
           -> Tot uint16
let op_Slash (UInt16 i) (UInt16 j) = UInt16 (i / j)

//a ?% b cannot overflow
val op_Percent: i:uint16
             -> j:uint16{as_int j <> 0}
             -> Tot uint16
let op_Percent (UInt16 i) (UInt16 j) = UInt16 (i % j)

val op_Less_Equals: i:uint16
                 -> j:uint16
                 -> Tot bool
let op_Less_Equals (UInt16 i) (UInt16 j) = i <= j

val op_Less: i:uint16
          -> j:uint16
          -> Tot bool
let op_Less (UInt16 i) (UInt16 j) = (i < j)

val op_Greater_Equals: i:uint16
                    -> j:uint16
                    -> Tot bool
let op_Greater_Equals (UInt16 i) (UInt16 j) = i >= j

val op_Greater: i:uint16
             -> j:uint16
             -> Tot bool
let op_Greater (UInt16 i) (UInt16 j) = i > j
