(*--build-config
    options:--logQueries;
 --*)
module FStar.BoundedIntegers

val int32_min_value : int
let int32_min_value = -2147483647

val int32_max_value : int
let int32_max_value = 2147483647

assume val uint32_max_value : int
(*let uint32_max_value = 4294967295*)

opaque logic type Within_Int32 (i:int) =
    int32_min_value <= i /\ i <= int32_max_value

private opaque logic type Int32 (i:int) =
  Within_Int32 i

opaque logic type Within_UInt32 (i:int) =
    0 <= i /\ i <= uint32_max_value

private opaque logic type UInt32 (i:int) =
   Within_UInt32 i

type int32 = i:int{Int32 i}
type uint32 = i:int{UInt32 i}

val int32_unfold: i:int
               -> Lemma
               (requires (Int32 i))
               (ensures (Within_Int32 i))
               [SMTPatT (Int32 i)]
let int32_unfold i = ()

val uint32_unfold: i:int
               -> Lemma
               (requires (UInt32 i))
               (ensures (Within_UInt32 i))
               [SMTPatT (UInt32 i)]
let uint32_unfold i = ()

val int32_add:i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i + j)
            ==> Int32 (i + j)))
  [SMTPatT (Int32 (i + j))]
let int32_add i j = ()

val int32_sub:i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i - j)
            ==> Int32 (i - j)))
  [SMTPatT (Int32 (i - j))]
let int32_sub i j = ()

val int32_mul:i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i * j)
            ==> Int32 (i * j)))
  [SMTPatT (Int32 (i * j))]
let int32_mul i j = ()

val int32_div:i:nat
          -> j:nonzero
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i / j)
            ==> Int32 (i / j)))
  [SMTPatT (Int32 (i / j))]
let int32_div i j = ()

(*val int32_op: op:(int -> int -> Tot int)
          -> i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (op i j)
            ==> Int32 (op i j)))
  [SMTPatT (Int32 (op i j))]
let int32_op op i j = ()

val uint32_op: op:(int -> int -> Tot int)
            -> i:int
            -> j:int
            -> Lemma
  (requires True)
  (ensures (UInt32 i /\ UInt32 j /\ Within_UInt32 (op i j)
            ==> UInt32 (op i j)))
  [SMTPatT (UInt32 (op i j))]
let uint32_op op i j = ()*)

module Test
open BoundedIntegers
let x : int32 = 1l
let y : int32 = 2l

let g (x:int32) : int32 = if x < BoundedIntegers.int32_max_value then x + 1l else x
let f (x:int32{0 <= x}) (y:int32{0 <= y /\ y <= x}) : int32 = x - ((x - y) / 2l)
let h (x:int32{0 <= x}) (y:int32{0 <= y /\ y <= x}) : int32 = (x + y) / 2l

(*
Int32 is an immutable value type that represents signed integers with values
that range from negative 2,147,483,648 (which is represented by the
Int32.MinValue constant) through positive 2,147,483,647 (which is represented by
the Int32.MaxValue constant.

The .NET Framework also includes an unsigned 32-bit
integer value type, UInt32, which represents values that range from 0 to
4,294,967,295.
*)


type int32 =
