module FStar.UInt32
open FStar.Mul
val min_value_int : int
let min_value_int = 0

val max_value_int : int
let max_value_int = 4294967295

let within_uint32 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type uint32' =
  | UInt32 : i:int{within_uint32 i} -> uint32'

abstract type uint32 = uint32'

val min_value : uint32
let min_value = UInt32 min_value_int

val max_value : uint32
let max_value = UInt32 max_value_int

val as_int: i:uint32 -> GTot int
let as_int (UInt32 i) = i

//a ?+ b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Plus: i:uint32
              -> j:uint32
              -> Tot (k:uint32{within_uint32 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (UInt32 i) (UInt32 j) =
  if within_uint32 (i + j)
  then UInt32 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:uint32
          -> j:uint32{within_uint32 (as_int i + as_int j)}
          -> Tot uint32
let op_Plus (UInt32 i) (UInt32 j) = UInt32 (i + j)

//a ?- b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Subtraction: i:uint32
              -> j:uint32
              -> Tot (k:uint32{within_uint32 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (UInt32 i) (UInt32 j) =
  if within_uint32 (i - j)
  then UInt32 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:uint32
                 -> j:uint32{within_uint32 (as_int i - as_int j)}
                 -> Tot uint32
let op_Subtraction (UInt32 i) (UInt32 j) = UInt32 (i - j)

//a ?* b may overflow
//must be marked abstract because the body has an intentional admit
abstract val op_Question_Star:
                 i:uint32
              -> j:uint32
              -> Tot (k:uint32{within_uint32 (op_Multiply (as_int i) (as_int j)) ==> as_int k = op_Multiply (as_int i) (as_int j)})
let op_Question_Star (UInt32 i) (UInt32 j) =
  if within_uint32 (op_Multiply i j)
  then UInt32 (op_Multiply i j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:uint32
          -> j:uint32{within_uint32 (op_Multiply (as_int i) (as_int j))}
          -> Tot uint32
let op_Star (UInt32 i) (UInt32 j) = UInt32 (op_Multiply i j)

// division cannot overflow with unsigned integers
val op_Slash: i:uint32
           -> j:uint32{as_int j <> 0}
           -> Tot uint32
let op_Slash (UInt32 i) (UInt32 j) = UInt32 (i / j)

//a ?% b cannot overflow
val op_Percent: i:uint32
             -> j:uint32{as_int j <> 0}
             -> Tot uint32
let op_Percent (UInt32 i) (UInt32 j) = UInt32 (i % j)

val op_Less_Equals: i:uint32
                 -> j:uint32
                 -> Tot bool
let op_Less_Equals (UInt32 i) (UInt32 j) = i <= j

val op_Less: i:uint32
          -> j:uint32
          -> Tot bool
let op_Less (UInt32 i) (UInt32 j) = (i < j)

val op_Greater_Equals: i:uint32
                    -> j:uint32
                    -> Tot bool
let op_Greater_Equals (UInt32 i) (UInt32 j) = i >= j

val op_Greater: i:uint32
             -> j:uint32
             -> Tot bool
let op_Greater (UInt32 i) (UInt32 j) = i > j
