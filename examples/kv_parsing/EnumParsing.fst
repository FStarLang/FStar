(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module EnumParsing

open Parsing
open IntegerParsing
open Serializing
open PureParser
open Validator
open PureEncoder
open Serializer
open Slice

open FStar.Tactics
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

(*! Pure model *)

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

val parse_numbers_tag : parser numbers_tag
let parse_numbers_tag =
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

let parser_forget (#t:Type) (#rf1:t -> Type0) ($p:parser (v:t{rf1 v})) : parser t =
  fun input -> match p input with
            | Some (v, off) -> Some (v, off)
            | None -> None

let parse_numbers_data (t:numbers_tag) : parser numbers =
  if U8.eq t 0uy
    then parser_forget parse_Nothing
  else if U8.eq t 1uy
    then parser_forget parse_OneNum
  else parser_forget parse_TwoNums

let parse_numbers : parser numbers =
  parse_numbers_tag `and_then` parse_numbers_data

(*! Pure validator  *)

(* This didn't end up being necessary (eg, as an intermediary to verified
parsers), but it demonstrates using extrinsic correctness proofs for validators.

The equivalent approach doesn't work for the real parsers/validators since
there's no support for extrinsically verifying properties of code in the STATE
effect. *)

let pure_validator = input:bytes{length input < pow2 32} -> option (off:nat{off <= length input})

let validate_ok (#t:Type) (p: parser t) (v: pure_validator) : Type0 =
  forall (input: bytes{length input < pow2 32}).
    match v input with
    | Some off -> Some? (p input) /\
                 (let (_, off') = Some?.v (p input) in
                   off == off')
    | None -> True

let pure_validator' #t (p: parser t) = v:pure_validator{validate_ok p v}

let parser_forget_ok #t (#rf1:t -> Type0) (p: parser (v:t{rf1 v})) (v: pure_validator) :
  Lemma (requires (validate_ok p v))
        (ensures (validate_ok (parser_forget p) v))
  [SMTPat (validate_ok (parser_forget p) v)] = ()

let make_correct #t (p: parser t) (v:pure_validator) :
  Pure (pure_validator' p)
    (requires (validate_ok p v))
    (ensures (fun r -> True)) = v

#reset-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 1"

let validate_Nothing_pure = make_correct (parser_forget parse_Nothing)
                            (fun input -> Some 0)

let validate_OneNum_pure = make_correct (parser_forget parse_OneNum)
                           (fun input -> if length input < 4 then None else Some 4)

let validate_TwoNums_pure = make_correct (parser_forget parse_TwoNums)
                            (fun input -> if length input < 8 then None else Some 8)

let validate_numbers_data_pure (t:numbers_tag) : pure_validator' (parse_numbers_data t) =
  make_correct _
  (if U8.eq t 0uy
    then validate_Nothing_pure
  else if U8.eq t 1uy
    then validate_OneNum_pure
  else validate_TwoNums_pure)

#reset-options "--z3rlimit 30"

val seq_pure_validate (v1 v2: pure_validator) : pure_validator
let seq_pure_validate v1 v2 = fun input ->
  match v1 input with
  | Some off -> (match v2 (slice input off (length input)) with
               | Some off' -> Some (off+off')
               | None -> None)
  | None -> None

val lemma_seq_pure_validate_A2_ok
  (#t:Type) (#p: parser t) (v1: pure_validator' p)
  (#t':Type) (#p': parser t') (v2: pure_validator' p') :
  Lemma (forall t'' (f: t -> t' -> t'').
        validate_ok
          (p `and_then` (fun (v:t) -> p' `and_then` (fun (v':t') -> parse_ret (f v v'))))
          (seq_pure_validate v1 v2))
let lemma_seq_pure_validate_A2_ok #t #p v1 #t' #p' v2 = ()

val then_pure_check (#t:Type) (p: parser t) (v: t -> pure_validator) : pure_validator
let then_pure_check #t p v = fun input ->
  match p input with
  | Some (x, off) -> (match v x (slice input off (length input)) with
                    | Some off' -> Some (off+off')
                    | None -> None)
  | None -> None

val lemma_then_pure_check_ok
  (#t:Type) (#p: parser t)
  (#t':Type) (#p': t -> parser t') (v: (x:t -> pure_validator' (p' x))) :
  Lemma (validate_ok
          (p `and_then` p')
          (p `then_pure_check` v))
  [SMTPat (p `then_pure_check` v); SMTPat (p `and_then` p')]
let lemma_then_pure_check_ok #t #p #t' #p' v = ()

#reset-options

let validate_numbers_pure : pure_validator' parse_numbers =
  make_correct _
  (parse_numbers_tag `then_pure_check` validate_numbers_data_pure)

(*! Stateful validator *)

val parse_numbers_tag_st : parser_st (hide parse_numbers_tag)
let parse_numbers_tag_st = fun input ->
  match parse_u8_st input with
  | Some (tag, off) -> if U8.lt tag 3uy
                      then Some ((tag <: numbers_tag), off)
                      else None
  | None -> None

let parse_numbers_tag_st_nochk : parser_st_nochk (hide parse_numbers_tag) = fun input ->
  let (tag, off) = parse_u8_st_nochk input in
  ((tag <: numbers_tag), off)

// here's a monolithic implementation of the whole thing:
(*
let validate_numbers (input:bslice) : Stack (option (off:U32.t{U32.v off <= U32.v input.len}))
  (requires (fun h0 -> live h0 input))
  (ensures (fun h0 r h1 -> live h1 input /\
                        modifies_none h0 h1 /\
                        begin
                          let bs = as_seq h1 input in
                          match r with
                          | Some off -> validate_numbers_pure bs == Some (U32.v off)
                          | None -> True
                        end)) =
  match parse_numbers_tag_st input with
  | Some (tag, off) ->
    let input = advance_slice input off in
    if U8.eq tag 0uy
      then Some off
    else (admit(); if U8.eq tag 1uy
      then if U32.lt input.len 4ul then None else Some (U32.add off 4ul)
    else begin
      assert (U8.v tag == 2);
      if U32.lt input.len 8ul then None else Some (U32.add off 8ul)
    end)
  | None -> None
*)

let check_length (len:U32.t) (input:bslice) : Pure bool
  (requires True)
  (ensures (fun r -> r ==> U32.v input.len >= U32.v len)) = U32.lte len input.len

val validate_Nothing : stateful_validator (hide (parser_forget parse_Nothing))
let validate_Nothing = fun input -> Some 0ul

val validate_OneNum : stateful_validator (hide (parser_forget parse_OneNum))
let validate_OneNum = fun input ->
  if check_length 4ul input then Some 4ul else None

val validate_TwoNums : stateful_validator (hide (parser_forget parse_TwoNums))
let validate_TwoNums = fun input ->
  if check_length 8ul input then Some 8ul else None

// this function returns a pointer to a global function; probably better to do
// this inline than go through a function pointer
// XXX: these qualifiers don't get the right inlining into validate_numbers, which also has an and_check
// inline_for_extraction [@"substitute"]
let validate_numbers_data (t:numbers_tag) : stateful_validator (hide (parse_numbers_data t)) =
  if U8.eq t 0uy then
    validate_Nothing
  else if U8.eq t 1uy then
    validate_OneNum
  else validate_TwoNums

// so far unused, but allows switching between equivalent parsers
let coerce_validator #t (#p: parser t)
                        (#p': parser t{forall x. p x == p' x})
                        (v: stateful_validator (hide p)) : stateful_validator (hide p') =
  fun input -> match v input with
            | Some off -> Some off
            | None -> None

#reset-options "--z3rlimit 15"

inline_for_extraction [@"substitute"]
val and_check (#t:Type) (#t':Type) (p: parser t) (p': t -> parser t') (p_st: parser_st (hide p))
              (v: (x:t -> stateful_validator (hide (p' x))))
              : stateful_validator (hide (p `and_then` p'))
let and_check #t #t' p p' p_st v =
    fun input -> match p_st input with
              | Some (x, off) ->
                begin
                  match v x (advance_slice input off) with
                  | Some off' -> Some (U32.add off off')
                  | None -> None
                end
              | None -> None

#reset-options

let validate_numbers : stateful_validator (hide parse_numbers) =
    // XXX: parse_numbers_tag is not inferred from the type of
    // parse_numbers_tag_st

    // XXX: validate_numbers_data is legitimately used to get a function
    // pointer, but KreMLin doesn't keep track of the fact that it's curried and
    // requires a different application in C (validate_numbers_data(tag)(input)
    // vs validate_numbers_data(tag, input)).
    and_check parse_numbers_tag parse_numbers_data parse_numbers_tag_st validate_numbers_data

(*! Encoder (pure serialization) *)

val encode_numbers_tag: numbers_tag -> b:bytes{length b == 1}
let encode_numbers_tag t = Seq.create 1 t

val encode_Nothing : b:bytes{length b == 0}
let encode_Nothing = Seq.empty

val encode_OneNum : n:U32.t -> b:bytes{length b == 4}
let encode_OneNum n = encode_u32 n

val encode_TwoNums : n:U32.t -> m:U32.t -> b:bytes{length b == 8}
let encode_TwoNums n m = encode_u32 n `append` encode_u32 m

val encode_numbers_data: numbers -> b:bytes
let encode_numbers_data ns = match ns with
    | Nothing -> encode_Nothing
    | OneNum n -> encode_OneNum n
    | TwoNums n m -> encode_TwoNums n m

val encode_numbers: numbers -> b:bytes
let encode_numbers ns =
  encode_numbers_tag (numbers_tag_val ns) `append`
  encode_numbers_data ns

(*! Serializer *)

val ser_numbers_tag: tag:numbers_tag -> serializer (hide (encode_numbers_tag tag))
let ser_numbers_tag tag = ser_byte tag

val ser_Nothing : serializer (hide (encode_Nothing))
let ser_Nothing = fun buf -> Some 0ul

val ser_OneNum : n:U32.t -> serializer (hide (encode_OneNum n))
let ser_OneNum n = ser_u32 n

#reset-options "--z3rlimit 10"

val ser_TwoNums : n:U32.t -> m:U32.t -> serializer (hide (encode_TwoNums n m))
let ser_TwoNums n m = fun buf -> (ser_u32 n `ser_append` ser_u32 m) buf

inline_for_extraction
let serializer_ty  = buf:bslice -> Stack (option (offset_into buf))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf))

let ser_TwoNums' (n m:U32.t) : serializer_ty =
  ser_TwoNums n m

let unfold_only (ns:list (list string)) : Tot (list norm_step) =
  FStar.List.Tot.map delta_only ns

#reset-options "--lax"

let ser_TwoNums'' (n m:U32.t) : serializer_ty =
  synth_by_tactic (fun () ->
                      normalize [delta_only
                      ["EnumParsing.ser_TwoNums";
                      "Serializing.ser_append"]] (ser_TwoNums n m <: serializer_ty))

#reset-options

// this works, but perhaps it should be eta expanded for extraction purposes
val ser_numbers_data: ns:numbers -> serializer (hide (encode_numbers_data ns))
let ser_numbers_data ns =
  match ns with
  | Nothing -> ser_Nothing
  | OneNum n -> ser_OneNum n
  | TwoNums n m -> ser_TwoNums n m

val ser_numbers_data': numbers -> serializer_ty
let ser_numbers_data' ns =
  fun buf -> match ns with
          | Nothing -> ser_Nothing buf
          | OneNum n -> ser_OneNum n buf
          | TwoNums n m -> ser_TwoNums n m buf


// this works ...
val ser_numbers_data2: ns:numbers -> serializer_ty 
let ser_numbers_data2 ns =
  match ns with
  | Nothing -> ser_Nothing
  | OneNum n -> ser_OneNum n
  | TwoNums n m -> ser_TwoNums n m

//but doing it via tactic normalization does not; NS/JR/JP: We added the --lax on 09/14
// this is the same as ser_numbers_data; haven't synthesized the eta expansion
#set-options "--lax"
let ser_numbers_data'' ns : serializer_ty =
    synth_by_tactic (fun () ->
                        normalize' [delta_only
                                   ["EnumParsing.ser_numbers_data2"]] (ser_numbers_data2 ns))

#reset-options
val ser_numbers: ns:numbers -> serializer (hide (encode_numbers ns))
let ser_numbers ns = fun buf ->
  (ser_numbers_tag (numbers_tag_val ns) `ser_append`
   ser_numbers_data ns) buf

//same problem as ser_numbers_data''
#set-options "--lax"
let ser_numbers' ns : serializer_ty =
  synth_by_tactic (fun () -> normalize' [delta_only
                             ["EnumParsing.ser_numbers";
                              "Serializing.ser_append"]] (ser_numbers ns <: serializer_ty))
