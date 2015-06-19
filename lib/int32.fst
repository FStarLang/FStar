(*--build-config
  --*)
module Int32
val int32_min_value_int : int
let int32_min_value_int = -2147483647

val int32_max_value_int : int
let int32_max_value_int = 2147483647

opaque type WithinInt32 (i:int) =
    int32_min_value_int <= i /\ i <= int32_max_value_int

private type int32 = i:int{WithinInt32 i}

val as_int: i:int32 -> GTot int
let as_int i = i

type nat32 = x:int32{Prims.op_GreaterThanOrEqual (as_int x) 0}

assume Int32_bound: forall (x:int32). WithinInt32 (as_int x)

opaque val op_Plus: i:int32
          -> j:int32{WithinInt32 (as_int i + as_int j)}
          -> Tot (k:int32{k=as_int i + as_int j})
let op_Plus i j = i + j

opaque val op_Subtraction: i:int32
                 -> j:int32{WithinInt32 (as_int i - as_int j)}
                 -> Tot (k:int32{k=as_int i - as_int j})
let op_Subtraction i j = i - j

opaque val op_Multiply:    i:int32
                 -> j:int32{WithinInt32 (as_int i * as_int j)}
                 -> Tot (k:int32{k=as_int i * as_int j})
let op_Multiply i j = i * j

opaque val op_Slash: i:int32{as_int i >= 0}
                  -> j:int32{as_int j <> 0 /\ WithinInt32 (as_int i / as_int j)}
                  -> Tot (k:int32{k = as_int i / as_int j})
let op_Slash i j = i / j

opaque val op_Less_Equals:    i:int32
                    -> j:int32
                    -> Tot (b:bool{b=(as_int i <= as_int j)})
let op_Less_Equals i j = i <= j

opaque val op_Less:           i:int32
                    -> j:int32
                    -> Tot (b:bool{b=(as_int i < as_int j)})
let op_Less i j = i < j

opaque val op_Greater_Equals: i:int32
                    -> j:int32
                    -> Tot (b:bool{b=(as_int i >= as_int j)})
let op_Greater_Equals i j = i >= j

opaque val op_Greater:        i:int32
                    -> j:int32
                    -> Tot (b:bool{b = (as_int i > as_int j)})
let op_Greater i j = i > j

opaque val op_Modulus: i:int32
            ->  j:int32{as_int j <> 0 /\ WithinInt32 (as_int i % as_int j)}
            ->  Tot (k:int32{k=as_int i % as_int j})
let op_Modulus i j = i % j

opaque val int32_min_value : i:int32{i=as_int int32_min_value_int}
let int32_min_value = int32_min_value_int

opaque val int32_max_value : i:int32{i=as_int int32_max_value_int}
let int32_max_value = int32_max_value_int
