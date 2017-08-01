module EnumParsing

open PureParser
open Validator
open Serializer
open Slice

open FStar.HyperStack
open FStar.HyperStack.ST

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
  parse_ret Nothing

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

let parse_numbers_tag_st : parser_st parse_numbers_tag = fun input ->
  match parse_u8_st input with
  | Some (tag, off) -> if U8.lt tag 3uy
                      then Some ((tag <: numbers_tag), off)
                      else None
  | None -> None

let parse_numbers_tag_st_nochk : parser_st_nochk parse_numbers_tag = fun input ->
  let (tag, off) = parse_u8_st_nochk input in
  ((tag <: numbers_tag), off)

let check_length (len:U32.t) (input:bslice) : Pure bool
  (requires True)
  (ensures (fun r -> r ==> U32.v input.len >= U32.v len)) = U32.lte len input.len

val validate_OneNum : stateful_validator parse_OneNum
let validate_OneNum = fun input ->
  if check_length 4ul input then Some 4ul else None

val validate_TwoNums : stateful_validator parse_TwoNums
let validate_TwoNums = fun input ->
  if check_length 8ul input then Some 8ul else None

#reset-options "--z3rlimit 10"

let validate_numbers : stateful_validator parse_numbers = fun input ->
  match parse_numbers_tag_st input with
  | Some (tag, off) -> if U8.eq tag 0uy
                        then Some off
                      else if U8.eq tag 1uy
                        then match validate_OneNum (advance_slice input off) with
                             | Some off' -> if u32_add_overflows off off' then None else Some (U32.add off off')
                             | None -> None
                      else begin
                             assert (U8.v tag == 2);
                             match validate_TwoNums (advance_slice input off) with
                             | Some off' -> if u32_add_overflows off off' then None else Some (U32.add off off')
                             | None -> None
                           end
  | None -> None
