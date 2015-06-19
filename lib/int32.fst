(*--build-config
  --*)
module Int32
val int32_min_value_int : int
let int32_min_value_int = -2147483648

val int32_max_value_int : int
let int32_max_value_int = 2147483647

opaque type WithinInt32 (i:int) =
    int32_min_value_int <= i /\ i <= int32_max_value_int

private type int32 =
  | Int32 : i:int{WithinInt32 i} -> int32

val as_int: i:int32 -> Tot int
let as_int (Int32 i) = i

type nat32 = x:int32{Prims.op_GreaterThanOrEqual (as_int x) 0}

assume Int32_bound: forall (x:int32). WithinInt32 (as_int x)

opaque val op_Plus: i:int32
          -> j:int32{WithinInt32 (as_int i + as_int j)}
          -> Tot (k:int32{as_int k=as_int i + as_int j})
let op_Plus (Int32 i) (Int32 j) = Int32 (i + j)

opaque val op_Subtraction: i:int32
                 -> j:int32{WithinInt32 (as_int i - as_int j)}
                 -> Tot (k:int32{as_int k=as_int i - as_int j})
let op_Subtraction (Int32 i) (Int32 j) = Int32 (i - j)

opaque val op_Star:    i:int32
                 -> j:int32{WithinInt32 (as_int i * as_int j)}
                 -> Tot (k:int32{as_int k=as_int i * as_int j})
let op_Star (Int32 i) (Int32 j) = Int32 (i * j)

opaque val op_Slash: i:int32{as_int i >= 0}
                  -> j:int32{as_int j <> 0 /\ WithinInt32 (as_int i / as_int j)}
                  -> Tot (k:int32{as_int k = as_int i / as_int j})
let op_Slash (Int32 i) (Int32 j) = Int32 (i / j)

opaque val op_Less_Equals: i:int32
                        -> j:int32
                        -> Tot (b:bool{b=(as_int i <= as_int j)})
let op_Less_Equals (Int32 i) (Int32 j) = i <= j

opaque val op_Less:    i:int32
                    -> j:int32
                    -> Tot (b:bool{b=(as_int i < as_int j)})
let op_Less (Int32 i) (Int32 j) = i < j

opaque val op_Greater_Equals: i:int32
                           -> j:int32
                           -> Tot (b:bool{b=(as_int i >= as_int j)})
let op_Greater_Equals (Int32 i) (Int32 j) = i >= j

opaque val op_Greater: i:int32
                    -> j:int32
                    -> Tot (b:bool{b = (as_int i > as_int j)})
let op_Greater (Int32 i) (Int32 j) = i > j

opaque val op_Percent: i:int32
                   ->  j:int32{as_int j <> 0 /\ WithinInt32 (as_int i % as_int j)}
                   ->  Tot (k:int32{as_int k=as_int i % as_int j})
let op_Percent (Int32 i) (Int32 j) = Int32 (i % j)

opaque val int32_min_value : i:int32{as_int i=int32_min_value_int}
let int32_min_value = Int32 int32_min_value_int

opaque val int32_max_value : i:int32{as_int i=int32_max_value_int}
let int32_max_value = Int32 int32_max_value_int
