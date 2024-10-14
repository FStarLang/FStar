module FStar_Char
open Prims

type char = FSharp.Core.char

let lowercase = System.Char.ToLower
let uppercase = System.Char.ToUpper
let int_of_char (x:char) : int = Microsoft.FSharp.Core.Operators.int x |> System.Numerics.BigInteger.op_Implicit
let char_of_int (x:int) : char = Microsoft.FSharp.Core.Operators.int x |> Microsoft.FSharp.Core.Operators.char
