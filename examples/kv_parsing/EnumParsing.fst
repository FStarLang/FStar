module EnumParsing

open PureParser
open Validator
open Serializer

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

type numbers =
  | Nothing : numbers
  | OneNum : n:U32.t -> numbers
  | TwoNums : n:U32.t -> m:U32.t -> numbers

// note that the choice of tags is part of the data format, so this still
// specifies encoding

// we might have needed a U16 even with 3 constructors if one of the tags was
// [>=256]
// the refinement is a simplification of all the legal tag values (in
// general might need to combine a bunch of ranges)
// NOTE: this could well just be a [nat] with a similar refinement
let numbers_tag = t:U8.t{U8.v t < 3}

val numbers_tag_val : numbers -> numbers_tag
let numbers_tag_val n =
  match n with
  | Nothing -> 0uy
  | OneNum _ -> 1uy
  | TwoNums _ _ -> 2uy

let parse_numbers_tag : parser numbers_tag =
  parse_u8 `and_then`
  (fun t -> if U8.lt t 3uy then parse_ret (t <: numbers_tag) else fail_parser)

let parse_Nothing : parser (ns:numbers{Nothing? ns}) =
  parse_ret #(ns:numbers{Nothing? ns}) Nothing

let parse_OneNum : parser (ns:numbers{OneNum? ns}) =
  parse_u32 `and_then`
  (fun n -> parse_ret #(ns:numbers{OneNum? ns}) (OneNum n))

let parse_TwoNums : parser (ns:numbers{TwoNums? ns}) =
  parse_u32 `and_then`
  (fun n -> parse_u32 `and_then`
  (fun m -> parse_ret #(ns:numbers{TwoNums? ns}) (TwoNums n m)))

let parse_numbers : parser numbers =
  parse_numbers_tag `and_then`
  (fun t -> if U8.eq t 0uy
            then parse_Nothing `and_then` parse_ret
         else if U8.eq t 1uy
           then parse_OneNum `and_then` parse_ret
         else // t == 2uy
           begin
            assert (U8.v t == 2);
            parse_TwoNums `and_then` parse_ret
           end)
