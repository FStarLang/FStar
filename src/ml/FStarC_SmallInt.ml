(* No .mli: other modules must see that [t = int], so that OCaml
   specializes comparisons and equality on it. *)
type t = int

let[@inline] of_int (x:Z.t) : t =
  if Obj.is_int (Obj.repr x) then (Obj.magic x : int) else Z.to_int x
let[@inline] to_int (x:t) : Z.t = Z.of_int x
let[@inline] of_char (c:FStar_Char.char) : t = c

let zero = 0
let one = 1
let minus_one = -1

let[@inline] op_Plus (a:t) (b:t) : t = a + b
let[@inline] op_Minus (a:t) (b:t) : t = a - b
let[@inline] op_Less (a:t) (b:t) : bool = a < b
let[@inline] op_Less_Equals (a:t) (b:t) : bool = a <= b
let[@inline] op_Greater (a:t) (b:t) : bool = a > b
let[@inline] op_Greater_Equals (a:t) (b:t) : bool = a >= b

let[@inline] max (a:t) (b:t) : t = if a >= b then a else b
let[@inline] min (a:t) (b:t) : t = if a <= b then a else b

let show (a:t) : string = string_of_int a

let[@inline] array_length (a:'a FStar_ImmutableArray_Base.t) : t = Array.length a
let[@inline] array_index (a:'a FStar_ImmutableArray_Base.t) (i:t) : 'a = Array.unsafe_get a i
