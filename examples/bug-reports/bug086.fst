(*--build-config
    options:--codegen OCaml;
  --*)
module Bug086

let x = 0

let xor = function 
  | (0, 1) 
  | (1, 0) -> 1
  | _ -> 0

val repr_bytes : nat -> Tot nat
let repr_bytes n =
     if n < 256 then 1
     else if n < 65536 then 2
     else if n < 16777216 then 3
     else if n < 4294967296 then 4
     else if n < 1099511627776 then 5
     else if n < 281474976710656 then 6
     else if n < 72057594037927936 then 7
     else 8

val f : unit -> GTot unit
let f () = ()

val repr_bytes2 : nat -> GTot nat
let repr_bytes2 n =
      let x = f () in
      if n < 256 then 1
      else if n < 65536 then 2
      else if n < 16777216 then 3
      else if n < 4294967296 then 4
      else if n < 1099511627776 then 5
      else if n < 281474976710656 then 6
      else if n < 72057594037927936 then 7
      else 8


val grepr_bytes : nat -> nat -> GTot nat
let grepr_bytes n _ =
      if n < 256 then 1
      else if n < 65536 then 2
      else if n < 16777216 then 3
      else if n < 4294967296 then 4
      else if n < 1099511627776 then 5
      else if n < 281474976710656 then 6
      else if n < 72057594037927936 then 7
      else 8
