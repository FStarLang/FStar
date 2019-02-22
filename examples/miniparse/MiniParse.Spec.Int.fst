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
module MiniParse.Spec.Int
include MiniParse.Spec.Combinators

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Aux = MiniParse.Spec.Int.Aux

let parse_u8 : parser_spec U8.t = make_total_constant_size_parser 1 U8.t (fun x -> Seq.index x 0)

let serialize_u8 : serializer_spec parse_u8 = Serializer (fun x -> Seq.create 1 x)

let parse_u16_aux : (f: ((s: bytes { Seq.length s == 2 } ) -> GTot U16.t) { make_total_constant_size_parser_precond 2 U16.t f } ) =
  fun x -> Aux.decode_u16 (Seq.index x 0, Seq.index x 1)

let parse_u16 : parser_spec U16.t = make_total_constant_size_parser 2 U16.t parse_u16_aux

let serialize_u16' : bare_serializer U16.t = fun x ->
  let (lo, hi) = Aux.encode_u16 x in
  Seq.append (Seq.create 1 lo) (Seq.create 1 hi)

#set-options "--z3rlimit 16"

let serialize_u16 : serializer_spec parse_u16 = Serializer serialize_u16'

#reset-options

inline_for_extraction
let mk_u16 (n: nat { n < 65536 } ) : Tot U16.t = U16.uint_to_t n

inline_for_extraction
let bounded_u16 (b: nat) : Tot eqtype = (x: U16.t { U16.v x < b } )

inline_for_extraction
let bounded_fun (a: Type) (b: nat) : Tot Type =
  a -> Tot (bounded_u16 b)

inline_for_extraction
let map_u16_to_bounded_u16
  (a: Type)
  (bound: nat)
  (f: (a -> Tot U16.t))
  (g: (x: a) -> Tot (squash (U16.v (f x) < bound)))
  (a' : Type)
  (bound' : nat)
  (u1: squash (a == a'))
  (u2: squash (bound == bound'))
: Tot (bounded_fun a' bound')
= fun x ->
  [@inline_let]
  let _ = g x in
  [@inline_let]
  let y' : bounded_u16 bound = f x in
  y'

let pred_pre
  (bound: nat { bound > 0 /\ bound <= 65536 } )
  (pred: bounded_u16 bound -> GTot Type0)
  (x: bounded_u16 (bound - 1))
: GTot Type0
= pred (x `U16.add` 1us)

let pred_large_bound
  (bound: nat { bound > 65536 } )
  (pred: bounded_u16 bound -> GTot Type0)
  (x: bounded_u16 (bound - 1))
: GTot Type0
= pred (x <: U16.t)

let rec forall_bounded_u16
  (bound: nat)
  (pred: (bounded_u16 bound -> GTot Type0))
: GTot Type0
= if bound = 0
  then True
  else if bound > 65536
  then
    forall_bounded_u16 (bound - 1) (pred_large_bound bound pred)
  else
    pred 0us /\ forall_bounded_u16 (bound - 1) (pred_pre bound pred)

let rec forall_bounded_u16_elim
  (bound: nat)
  (pred: (bounded_u16 bound -> GTot Type0))
  (x: bounded_u16 bound)
: Lemma
  (requires (forall_bounded_u16 bound pred))
  (ensures (pred x))
  (decreases bound)
= if bound = 0
  then ()
  else if bound > 65536
  then
    let x' : bounded_u16 (bound - 1) = x <: U16.t in
    forall_bounded_u16_elim (bound - 1) (pred_large_bound bound pred) x'
  else if x = 0us
  then ()
  else
    forall_bounded_u16_elim (bound - 1) (pred_pre bound pred) (x `U16.sub` 1us)

inline_for_extraction
let bounded_u16_eq (b: nat) : Tot (bounded_u16 b -> bounded_u16 b -> Tot bool) =
  op_Equality

let parse_bounded_u16 (b: nat) : Tot (parser_spec (bounded_u16 b)) =
  parse_synth
    (parse_filter parse_u16 (fun x -> U16.v x < b))
    (fun x -> x <: bounded_u16 b)
    (fun x -> x)

let serialize_bounded_u16 (b: nat) : Tot (serializer_spec (parse_bounded_u16 b)) =
  serialize_synth
    (serialize_filter serialize_u16 (fun x -> U16.v x < b))
    (fun x -> x <: bounded_u16 b)
    (fun x -> x)
    ()
