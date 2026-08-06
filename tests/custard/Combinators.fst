(* Bundled parser combinators, in the style of EverParse 3D: a record of a
   parser and a serializer, built up by combinators.  Monomorphizing the two
   [parse]/[serialize] wrappers is enough to get one top-level function per
   (combinator, method) pair, each calling its sub-combinators directly --
   the [parser_combinator] record is never materialized at runtime. *)
module Combinators
module U32 = FStar.UInt32

assume val bytes : Type0
assume val get32 : bytes -> nat -> U32.t
assume val put32 : U32.t -> bytes
assume val concat : bytes -> bytes -> bytes
assume val slice : bytes -> nat -> bytes

noeq
type parser_combinator (ty:Type0) = {
  parse: bytes -> option (nat & ty);
  serialize: ty -> bytes;
}

(* The two monomorphizing wrappers. *)
let parse (#a:Type0) ([@@@monomorphize] p: parser_combinator a) (b:bytes)
  : option (nat & a) = p.parse b

let serialize (#a:Type0) ([@@@monomorphize] p: parser_combinator a) (x:a)
  : bytes = p.serialize x

let u32 : parser_combinator U32.t = {
  parse = (fun b -> Some (4, get32 b 0));
  serialize = (fun x -> put32 x);
}

let seq (#a #b:Type0) (p: parser_combinator a) (q: parser_combinator b)
  : parser_combinator (a & b)
  = {
      parse = (fun bs ->
        match parse p bs with
        | None -> None
        | Some (n, x) ->
          (match parse q (slice bs n) with
           | None -> None
           | Some (m, y) -> Some (n + m, (x, y))));
      serialize = (fun (x, y) -> concat (serialize p x) (serialize q y));
    }

let three_numbers : parser_combinator (U32.t & (U32.t & U32.t)) =
  seq u32 (seq u32 u32)

let parse_three (bs:bytes) : option (nat & (U32.t & (U32.t & U32.t))) =
  parse three_numbers bs

let serialize_three (x: U32.t & (U32.t & U32.t)) : bytes =
  serialize three_numbers x
