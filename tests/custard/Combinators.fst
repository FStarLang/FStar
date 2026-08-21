(* Bundled parser combinators, in the style of EverParse 3D: a record of a
   parser and a serializer, built up by combinators.  Monomorphizing the two
   [parse]/[serialize] wrappers is enough to get one top-level function per
   (combinator, method) pair, each calling its sub-combinators directly --
   the [parser_combinator] record is never materialized at runtime.  See
   section 3.9. *)
module Combinators
open FStar.All
open FStar.IO

module U32 = FStar.UInt32

(* A byte string, one 32-bit word per position: what a real parser does with
   the bytes is not what this test is about. *)
type bytes = list U32.t

let rec get32 (b:bytes) (i:nat) : U32.t =
  match b with
  | [] -> 0ul
  | x :: tl -> if i = 0 then x else get32 tl (i - 1)

let put32 (x:U32.t) : bytes = [x]

let rec concat (b c:bytes) : bytes =
  match b with
  | [] -> c
  | x :: tl -> x :: concat tl c

let rec slice (b:bytes) (n:nat) : bytes =
  match b with
  | [] -> []
  | _ :: tl -> if n = 0 then b else slice tl (n - 1)

noeq
type parser_combinator (ty:Type0) = {
  parse: bytes -> option (nat & ty);
  serialize: ty -> bytes;
}

(* The two monomorphizing wrappers.  [seq] below needs no annotation of its
   own: rule 5 of section 3.1 propagates [Mono] to any binder that flows into
   a [Mono] position. *)
let parse (#a:Type0) ([@@@monomorphize] p: parser_combinator a) (b:bytes)
  : option (nat & a) = p.parse b

let serialize (#a:Type0) ([@@@monomorphize] p: parser_combinator a) (x:a)
  : bytes = p.serialize x

let u32 : parser_combinator U32.t = {
  parse = (fun b -> Some (1, get32 b 0));
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

let main () : ML unit =
  let v = (0x01020304ul, (7ul, 0xfffffffful)) in
  match parse_three (serialize_three v) with
  | None -> print_string "FAIL: no parse\n"
  | Some (n, (a, (b, c))) ->
    print_string (string_of_int n); print_string " ";
    print_string (U32.to_string a); print_string " ";
    print_string (U32.to_string b); print_string " ";
    print_string (U32.to_string c); print_string "\n"
