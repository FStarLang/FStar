module Calc.Wire

(** Wire format for calculator protocol **)

module B = FStar.Bytes
module U8 = FStar.UInt8
module Seq = FStar.Seq

type bytes = Seq.seq U8.t

(** Request operations **)
type request =
  | Push of int
  | Peek
  | Add
  | Sub
  | Mul
  | Div

(** Response messages **)
type response =
  | Ok
  | Result of int
  | Error

(** Wire encoding: 5 bytes per message **)
(** [tag:1][data:4] where data is big-endian int **)

let be_to_n (b:bytes{Seq.length b == 4}) : int =
  let open U8 in
  let b0 = v (Seq.index b 0) in
  let b1 = v (Seq.index b 1) in
  let b2 = v (Seq.index b 2) in
  let b3 = v (Seq.index b 3) in
  b0 * 16777216 + b1 * 65536 + b2 * 256 + b3

let n_to_be (x:int) : b:bytes{Seq.length b == 4} =
  let open U8 in
  let b0 = uint_to_t ((x / 16777216) % 256) in
  let b1 = uint_to_t ((x / 65536) % 256) in
  let b2 = uint_to_t ((x / 256) % 256) in
  let b3 = uint_to_t (x % 256) in
  let s = Seq.create 4 b0 in
  let s = Seq.upd s 1 b1 in
  let s = Seq.upd s 2 b2 in
  Seq.upd s 3 b3

val parse_request (b:bytes{Seq.length b == 5}) : option request

let parse_request b =
  let tag = U8.v (Seq.index b 0) in
  let data_bytes = Seq.slice b 1 5 in
  let data = be_to_n data_bytes in
  match tag with
  | 0 -> Some (Push data)
  | 1 -> Some Peek
  | 2 -> Some Add
  | 3 -> Some Sub
  | 4 -> Some Mul
  | 5 -> Some Div
  | _ -> None

val serialize_response (r:response) : b:bytes{Seq.length b == 5}

let serialize_response r =
  let tag, data = match r with
    | Ok -> 0, 0
    | Result x -> 1, x
    | Error -> 2, 0
  in
  let tag_byte = U8.uint_to_t tag in
  let data_bytes = n_to_be data in
  Seq.cons tag_byte data_bytes

(** Helper lemmas for response serialization **)
val lemma_serialize_ok_bytes 
  (b: bytes{Seq.length b == 5 /\ Seq.index b 0 == 0uy})
  : Lemma (requires Seq.index b 1 == 0uy /\ Seq.index b 2 == 0uy /\
                    Seq.index b 3 == 0uy /\ Seq.index b 4 == 0uy)
          (ensures serialize_response Ok `Seq.equal` b)

let lemma_serialize_ok_bytes b =
  let sr = serialize_response Ok in
  assert (Seq.index sr 0 == 0uy);
  assert (Seq.index sr 1 == 0uy);
  assert (Seq.index sr 2 == 0uy);
  assert (Seq.index sr 3 == 0uy);
  assert (Seq.index sr 4 == 0uy);
  assert (Seq.index b 0 == 0uy);
  assert (Seq.index b 1 == 0uy);
  assert (Seq.index b 2 == 0uy);
  assert (Seq.index b 3 == 0uy);
  assert (Seq.index b 4 == 0uy)

val lemma_serialize_error_bytes 
  (b: bytes{Seq.length b == 5 /\ Seq.index b 0 == 2uy})
  : Lemma (requires Seq.index b 1 == 0uy /\ Seq.index b 2 == 0uy /\
                    Seq.index b 3 == 0uy /\ Seq.index b 4 == 0uy)
          (ensures serialize_response Error `Seq.equal` b)

let lemma_serialize_error_bytes b =
  let sr = serialize_response Error in
  assert (Seq.index sr 0 == 2uy);
  assert (Seq.index sr 1 == 0uy);
  assert (Seq.index sr 2 == 0uy);
  assert (Seq.index sr 3 == 0uy);
  assert (Seq.index sr 4 == 0uy);
  assert (Seq.index b 0 == 2uy);
  assert (Seq.index b 1 == 0uy);
  assert (Seq.index b 2 == 0uy);
  assert (Seq.index b 3 == 0uy);
  assert (Seq.index b 4 == 0uy)

val lemma_serialize_result_bytes
  (x: int)
  (b: bytes{Seq.length b == 5 /\ Seq.index b 0 == 1uy})
  : Lemma (requires be_to_n (Seq.slice b 1 5) == x)
          (ensures serialize_response (Result x) `Seq.equal` b)

(* Spelled out, rather than left to nonlinear SMT reasoning, which is
   unstable here. *)
let lemma_n_to_be_be_to_n (s:bytes{Seq.length s == 4})
  : Lemma (n_to_be (be_to_n s) `Seq.equal` s)
  = let open FStar.Math.Lemmas in
    let b0 = U8.v (Seq.index s 0) in
    let b1 = U8.v (Seq.index s 1) in
    let b2 = U8.v (Seq.index s 2) in
    let b3 = U8.v (Seq.index s 3) in
    let x = be_to_n s in
    let hi = b0 * 65536 + b1 * 256 + b2 in
    assert (x == b3 + hi * 256);
    lemma_mod_plus b3 hi 256;
    lemma_div_plus b3 hi 256;
    small_mod b3 256;
    small_div b3 256;
    assert (x % 256 == b3 /\ x / 256 == hi);
    let lo2 = b2 * 256 + b3 in
    let hi2 = b0 * 256 + b1 in
    assert (x == lo2 + hi2 * 65536);
    lemma_div_plus lo2 hi2 65536;
    small_div lo2 65536;
    lemma_mod_plus b2 (b0 * 256 + b1) 256;
    small_mod b2 256;
    lemma_mod_plus b1 b0 256;
    small_mod b1 256;
    let lo3 = b1 * 65536 + lo2 in
    assert (x == lo3 + b0 * 16777216);
    lemma_div_plus lo3 b0 16777216;
    small_div lo3 16777216;
    small_mod b0 256

let lemma_serialize_result_bytes x b =
  let sr = serialize_response (Result x) in
  lemma_n_to_be_be_to_n (Seq.slice b 1 5);
  assert (Seq.index sr 0 == 1uy);
  assert (Seq.slice sr 1 5 `Seq.equal` n_to_be x);
  assert (n_to_be x `Seq.equal` Seq.slice b 1 5)
