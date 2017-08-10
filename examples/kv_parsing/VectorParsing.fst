module VectorParsing

open PureParser
open Validator
open PureEncoder
open Serializer
open Slice

open FStar.Ghost
module List = FStar.List.Tot
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

assume type t : Type0
assume val parse_elem : parser t

assume val enc_elem : t -> b:bytes{length b > 0}

assume val parse_elem_enc : b:bytes{length b < pow2 32} ->
  Lemma (match parse_elem b with
        | Some (v, off) -> enc_elem v == slice b 0 off
        | None -> True)

val parse_elem_progress : b:bytes{length b < pow2 32} ->
  Lemma (match parse_elem b with
        | Some (_, off) -> off > 0
        | None -> True)
let parse_elem_progress b = parse_elem_enc b

val parse_elem_enc_length : b:bytes{length b < pow2 32} ->
  Lemma (match parse_elem b with
        | Some (v, off) -> length (enc_elem v) == off
        | None -> True)
let parse_elem_enc_length b = parse_elem_enc b

// for vector of length 0..2^16-1
// (note: no additional length checks, and this fixes the length field as a
// U16.t)

val vector_length: list t -> nat
let vector_length l = List.fold_right (fun v (acc: nat) -> length (enc_elem v) + acc) l 0

type vector = l:list t{vector_length l < pow2 16}

val parse_vector_length_pre : len:U16.t -> b:bytes{length b < pow2 32} ->
  Tot (option (v:vector{vector_length v == U16.v len}))
  (decreases (length b))
let rec parse_vector_length_pre len = fun b ->
  if length b <> U16.v len then None else
  if U16.v len = 0 then Some [] else
  match parse_elem b with
  | Some (v, off) ->
    parse_elem_progress b;
    parse_elem_enc_length b;
    begin
      let b = slice b off (length b) in
      match parse_vector_length_pre (U16.sub len (U16.uint_to_t off)) b with
      | Some vs -> Some (v::vs)
      | None -> None
    end
  | None -> None

val parse_vector_length : len:U16.t -> parser (v:vector{vector_length v == U16.v len})
let parse_vector_length len = fun b ->
  match parse_vector_length_pre len b with
  | Some v -> Some (v, U16.v len)
  | None -> None

val parse_vector_length_consumes_len : len:U16.t -> b:bytes{length b < pow2 32} ->
  Lemma (match parse_vector_length len b with
        | Some (_, off) -> off == U16.v len
        | None -> True)
let parse_vector_length_consumes_len len b = ()

val parse_vector : parser vector
let parse_vector =
  parse_u16 `and_then`
  (fun bytes -> parse_vector_length bytes `and_then`
  (fun v -> parse_ret (v <: vector)))

val encode_vector_data : v:vector -> b:bytes{length b == vector_length v}
let rec encode_vector_data v =
  match v with
  | [] -> createEmpty
  | e::es -> enc_elem e `append` encode_vector_data es

val encode_vector : v:vector -> bytes
let encode_vector v =
  u16_to_be (U16.uint_to_t (vector_length v)) `append`
  encode_vector_data v
