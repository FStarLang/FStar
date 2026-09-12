module CborBoundary

(* A reduced deterministic-CBOR well-formedness checker, in pure F* -- no
   Pulse, no LowParse, no krmllib -- so that Custard's direct-to-C backend
   can extract it as part of the every-push [tests/custard] suite.

   It is deliberately *not* the real EverParse parser.  It exists to keep
   exercising the four classes of behaviour that the curated CBOR corpus was
   built to hit, and that random input generation was measured not to reach:

     1. UTF-8 codepoint and continuation-byte boundaries,
     2. minimal-length integer encodings at each width boundary,
     3. declared element counts versus remaining input budget,
     4. truncation, i.e. proper prefixes of well-formed items.

   The input is a [ref]-linked cons cell rather than a slice, which is the
   shape [CRecType] already exercises.  Direct-to-C is perfectly capable of
   compiling a contiguous buffer -- a Pulse [let mut arr = [| ... |]] becomes
   a [uint8_t[N]] and a slice over it becomes a [{ uint8_t *elt; size_t len; }]
   -- but the array abstractions are Pulse libraries, and stage1 and stage2
   have no Pulse language extension while [make test-1] and [test-2] both run
   this directory.  So the every-push copy of this checker cannot take a
   buffer, and [pulse/CborBoundarySlice.fst] is the copy that does; see
   CborBoundary.md.

   [main] reports through its exit code, since direct-to-C has no krmllib
   and so no [FStar.IO.print_string] to link against. *)

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I32 = FStar.Int32
module Cast = FStar.Int.Cast

open FStar.All

type byte = U8.t

noeq type blist =
  | BNil
  | BCons : byte -> ref blist -> blist

let cons (b : byte) (t : blist) : ML blist = BCons b (alloc t)

let uncons (l : blist) : ML (option (byte & blist)) =
  match l with
  | BNil -> None
  | BCons b r -> Some (b, !r)

let in_range (lo hi x : byte) : Tot bool = U8.lte lo x && U8.lte x hi

let rec len64 (l : blist) : ML U64.t =
  match uncons l with
  | None -> 0UL
  | Some (_, t) ->
    let r = len64 t in
    if U64.lt r 0xFFFFFFFFFFFFFFFFUL then U64.add r 1UL else r

(* ------------------------------------------------------------------ *)
(* 1. UTF-8, per RFC 3629 table 3-7.                                   *)
(*                                                                     *)
(* The second-byte bounds are the point: [E0 A0..BF] and [F0 90..BF]   *)
(* reject overlong forms, [ED 80..9F] rejects surrogates, and          *)
(* [F4 80..8F] rejects anything above U+10FFFF.  A mutation can move   *)
(* any one of those four bounds without changing which lines execute,  *)
(* which is exactly why line coverage does not detect it.              *)
(*                                                                     *)
(* Validating a counted span rather than a whole list also makes       *)
(* truncation *inside* a multi-byte sequence reachable: a string whose *)
(* declared length stops between a lead byte and its continuations.    *)
(* ------------------------------------------------------------------ *)

let rec utf8_take (n : U64.t) (l : blist) : ML (option blist) =
  if U64.eq n 0UL then Some l
  else
    match uncons l with
    | None -> None
    | Some (b0, t0) ->
      if U8.lte b0 0x7Fuy then utf8_take (U64.sub n 1UL) t0
      else if in_range 0xC2uy 0xDFuy b0 then
        (if U64.lt n 2UL then None
         else
           match uncons t0 with
           | None -> None
           | Some (b1, t1) ->
             if in_range 0x80uy 0xBFuy b1 then utf8_take (U64.sub n 2UL) t1 else None)
      else if U8.eq b0 0xE0uy || U8.eq b0 0xEDuy
              || in_range 0xE1uy 0xECuy b0 || in_range 0xEEuy 0xEFuy b0 then
        (if U64.lt n 3UL then None
         else
           let lo1 = if U8.eq b0 0xE0uy then 0xA0uy else 0x80uy in
           let hi1 = if U8.eq b0 0xEDuy then 0x9Fuy else 0xBFuy in
           match uncons t0 with
           | None -> None
           | Some (b1, t1) ->
             if not (in_range lo1 hi1 b1) then None
             else
               match uncons t1 with
               | None -> None
               | Some (b2, t2) ->
                 if in_range 0x80uy 0xBFuy b2 then utf8_take (U64.sub n 3UL) t2
                 else None)
      else if in_range 0xF0uy 0xF4uy b0 then
        (if U64.lt n 4UL then None
         else
           let lo1 = if U8.eq b0 0xF0uy then 0x90uy else 0x80uy in
           let hi1 = if U8.eq b0 0xF4uy then 0x8Fuy else 0xBFuy in
           match uncons t0 with
           | None -> None
           | Some (b1, t1) ->
             if not (in_range lo1 hi1 b1) then None
             else
               match uncons t1 with
               | None -> None
               | Some (b2, t2) ->
                 if not (in_range 0x80uy 0xBFuy b2) then None
                 else
                   match uncons t2 with
                   | None -> None
                   | Some (b3, t3) ->
                     if in_range 0x80uy 0xBFuy b3 then utf8_take (U64.sub n 4UL) t3
                     else None)
      else None

(* ------------------------------------------------------------------ *)
(* 2. Header and argument decoding, with minimal-length enforcement.    *)
(* ------------------------------------------------------------------ *)

let rec take_be (n : U64.t) (acc : U64.t) (l : blist) : ML (option (U64.t & blist)) =
  if U64.eq n 0UL then Some (acc, l)
  else
    match uncons l with
    | None -> None
    | Some (b, t) ->
      take_be (U64.sub n 1UL)
              (U64.add_mod (U64.mul_mod acc 256UL) (Cast.uint8_to_uint64 b)) t

let rec drop (n : U64.t) (l : blist) : ML (option blist) =
  if U64.eq n 0UL then Some l
  else
    match uncons l with
    | None -> None
    | Some (_, t) -> drop (U64.sub n 1UL) t

(* Deterministic CBOR requires the shortest encoding of the argument.  Each
   width has its own lower bound; getting one wrong moves no lines. *)
let arg_is_minimal (ai : byte) (v : U64.t) : Tot bool =
  if U8.eq ai 24uy then U64.gte v 24UL
  else if U8.eq ai 25uy then U64.gte v 256UL
  else if U8.eq ai 26uy then U64.gte v 65536UL
  else if U8.eq ai 27uy then U64.gte v 4294967296UL
  else true

let decode_arg (ai : byte) (l : blist) : ML (option (U64.t & blist)) =
  if U8.lt ai 24uy then Some (Cast.uint8_to_uint64 ai, l)
  else if U8.eq ai 24uy then take_be 1UL 0UL l
  else if U8.eq ai 25uy then take_be 2UL 0UL l
  else if U8.eq ai 26uy then take_be 4UL 0UL l
  else if U8.eq ai 27uy then take_be 8UL 0UL l
  else None   (* 28..30 reserved, 31 indefinite: both forbidden here *)

(* ------------------------------------------------------------------ *)
(* 3. The item checker.                                                *)
(* ------------------------------------------------------------------ *)

let rec item (fuel : U64.t) (l : blist) : ML (option blist) =
  if U64.eq fuel 0UL then None
  else
    match uncons l with
    | None -> None
    | Some (b0, t0) ->
      let mt = U8.shift_right b0 5ul in
      let ai = U8.logand b0 0x1Fuy in
      (match decode_arg ai t0 with
       | None -> None
       | Some (v, rest) ->
         if not (arg_is_minimal ai v) then None
         else if U8.eq mt 0uy || U8.eq mt 1uy then Some rest
         else if U8.eq mt 2uy then drop v rest
         else if U8.eq mt 3uy then utf8_take v rest
         else if U8.eq mt 4uy then
           (* An array of [v] elements needs at least [v] more bytes.
              Checking before recursing is what stops a 2^64-element header
              from being explored. *)
           (if U64.gt v (len64 rest) then None
            else items (U64.sub fuel 1UL) v rest)
         else if U8.eq mt 5uy then
           (* A map of [v] pairs needs at least [2v] bytes.  The doubling is
              itself a boundary and can overflow, so it is written as a
              subtraction against the remaining budget. *)
           (let budget = len64 rest in
            if U64.gt v budget then None
            else if U64.gt v (U64.sub budget v) then None
            else items (U64.sub fuel 1UL) (U64.mul_mod v 2UL) rest)
         else if U8.eq mt 6uy then item (U64.sub fuel 1UL) rest
         else
           (* Major type 7.  Additional info 24 must carry a byte >= 32,
              because 0..23 are already expressible in the header itself. *)
           (if U8.lt ai 24uy then Some rest
            else if U8.eq ai 24uy then (if U64.gte v 32UL then Some rest else None)
            else None))

and items (fuel : U64.t) (n : U64.t) (l : blist) : ML (option blist) =
  if U64.eq fuel 0UL then None
  else if U64.eq n 0UL then Some l
  else
    match item (U64.sub fuel 1UL) l with
    | None -> None
    | Some rest -> items (U64.sub fuel 1UL) (U64.sub n 1UL) rest

let validate (l : blist) : ML bool =
  match item 64UL l with
  | None -> false
  | Some r -> (match uncons r with None -> true | Some _ -> false)

let v0 () : ML blist = cons 0xA3uy (cons 0x42uy (cons 0x6Fuy (cons 0xDDuy (cons 0xF8uy (cons 0x20uy (cons 0x45uy (cons 0x66uy (cons 0x72uy (cons 0xE7uy (cons 0x58uy (cons 0xB8uy (cons 0xD8uy (cons 0x64uy (cons 0x17uy (cons 0x60uy (cons 0x82uy (cons 0x39uy (cons 0xFFuy (cons 0xFFuy (cons 0xDBuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xF7uy (BNil))))))))))))))))))))))))))))))
let v1 () : ML blist = cons 0xDBuy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x01uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0xA2uy (cons 0x1Auy (cons 0x36uy (cons 0x42uy (cons 0xC8uy (cons 0x4Buy (cons 0xA3uy (cons 0x1Auy (cons 0x9Cuy (cons 0xF4uy (cons 0xDAuy (cons 0x8Buy (cons 0xF8uy (cons 0xFFuy (cons 0x45uy (cons 0xA2uy (cons 0xE6uy (cons 0x78uy (cons 0x37uy (cons 0xDFuy (cons 0x6Buy (cons 0xE4uy (cons 0xB8uy (cons 0xADuy (cons 0xC3uy (cons 0xA9uy (cons 0x5Auy (cons 0x62uy (cons 0xF0uy (cons 0x9Fuy (cons 0x98uy (cons 0x80uy (cons 0x65uy (cons 0x63uy (cons 0x64uy (cons 0x63uy (cons 0x65uy (cons 0x65uy (cons 0x44uy (cons 0x7Fuy (cons 0x6Duy (cons 0xF2uy (cons 0x24uy (cons 0x1Auy (cons 0xB6uy (cons 0x6Cuy (cons 0x10uy (cons 0x8Euy (cons 0x80uy (BNil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
let v2 () : ML blist = cons 0x61uy (cons 0x7Fuy (BNil))
let v3 () : ML blist = cons 0x62uy (cons 0xDFuy (cons 0xBFuy (BNil)))
let v4 () : ML blist = cons 0x63uy (cons 0xE0uy (cons 0xA0uy (cons 0x80uy (BNil))))
let v5 () : ML blist = cons 0x63uy (cons 0xEDuy (cons 0x9Fuy (cons 0xBFuy (BNil))))
let v6 () : ML blist = cons 0x63uy (cons 0xEEuy (cons 0x80uy (cons 0x80uy (BNil))))
let v7 () : ML blist = cons 0x63uy (cons 0xEFuy (cons 0xBFuy (cons 0xBFuy (BNil))))
let v8 () : ML blist = cons 0x64uy (cons 0xF0uy (cons 0x90uy (cons 0x80uy (cons 0x80uy (BNil)))))
let v9 () : ML blist = cons 0x64uy (cons 0xF4uy (cons 0x8Fuy (cons 0xBFuy (cons 0xBFuy (BNil)))))
let v10 () : ML blist = cons 0x63uy (cons 0xE1uy (cons 0x80uy (cons 0x80uy (BNil))))
let v11 () : ML blist = cons 0xA2uy (cons 0x18uy (cons 0x18uy (cons 0x00uy (cons 0x61uy (cons 0x61uy (cons 0x01uy (BNil)))))))
let v12 () : ML blist = cons 0x1Auy (cons 0x00uy (cons 0x01uy (cons 0x00uy (cons 0x00uy (BNil)))))
let v13 () : ML blist = cons 0x39uy (cons 0x01uy (cons 0x00uy (BNil)))
let v14 () : ML blist = cons 0x64uy (cons 0xF1uy (cons 0x80uy (cons 0x80uy (cons 0x80uy (BNil)))))
let v15 () : ML blist = cons 0x62uy (cons 0xC2uy (cons 0x80uy (BNil)))
let v16 () : ML blist = cons 0xA0uy (BNil)
let v17 () : ML blist = cons 0x80uy (BNil)
let v18 () : ML blist = cons 0x81uy (cons 0x00uy (BNil))
let v19 () : ML blist = cons 0x82uy (cons 0x00uy (cons 0x01uy (BNil)))
let v20 () : ML blist = cons 0x83uy (cons 0x00uy (cons 0x01uy (cons 0x02uy (BNil))))
let v21 () : ML blist = cons 0xA1uy (cons 0x00uy (cons 0x00uy (BNil)))
let v22 () : ML blist = cons 0xA2uy (cons 0x00uy (cons 0x00uy (cons 0x01uy (cons 0x01uy (BNil)))))
let v23 () : ML blist = cons 0xA3uy (cons 0x00uy (cons 0x00uy (cons 0x01uy (cons 0x01uy (cons 0x02uy (cons 0x02uy (BNil)))))))
let v24 () : ML blist = cons 0x63uy (cons 0xE1uy (cons 0xBFuy (cons 0x80uy (BNil))))
let v25 () : ML blist = cons 0x64uy (cons 0xF1uy (cons 0xBFuy (cons 0x80uy (cons 0x80uy (BNil)))))
let v26 () : ML blist = cons 0x64uy (cons 0xF4uy (cons 0x90uy (cons 0x80uy (cons 0x80uy (BNil)))))
let v27 () : ML blist = cons 0x63uy (cons 0xEDuy (cons 0xA0uy (cons 0x80uy (BNil))))
let v28 () : ML blist = cons 0x62uy (cons 0xC1uy (cons 0xBFuy (BNil)))
let v29 () : ML blist = cons 0x62uy (cons 0xC2uy (cons 0x7Fuy (BNil)))
let v30 () : ML blist = cons 0x63uy (cons 0xE0uy (cons 0x9Fuy (cons 0xBFuy (BNil))))
let v31 () : ML blist = cons 0x64uy (cons 0xF0uy (cons 0x8Fuy (cons 0x80uy (cons 0x80uy (BNil)))))
let v32 () : ML blist = cons 0x64uy (cons 0xF5uy (cons 0x80uy (cons 0x80uy (cons 0x80uy (BNil)))))
let v33 () : ML blist = cons 0x61uy (cons 0x80uy (BNil))
let v34 () : ML blist = cons 0x64uy (cons 0xF0uy (cons 0x90uy (cons 0xC0uy (cons 0x80uy (BNil)))))
let v35 () : ML blist = cons 0x64uy (cons 0xF0uy (cons 0x90uy (cons 0x80uy (cons 0xC0uy (BNil)))))
let v36 () : ML blist = cons 0xF8uy (cons 0x1Fuy (BNil))
let v37 () : ML blist = cons 0x18uy (cons 0x17uy (BNil))
let v38 () : ML blist = cons 0x19uy (cons 0x00uy (cons 0xFFuy (BNil)))
let v39 () : ML blist = cons 0x1Auy (cons 0x00uy (cons 0x00uy (cons 0xFFuy (cons 0xFFuy (BNil)))))
let v40 () : ML blist = cons 0x3Buy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (cons 0xFFuy (BNil)))))))))
let v41 () : ML blist = cons 0x85uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (BNil)))))))
let v42 () : ML blist = cons 0x18uy (BNil)
let v43 () : ML blist = cons 0x19uy (cons 0xFFuy (BNil))
let v44 () : ML blist = cons 0x1Auy (cons 0x01uy (cons 0x00uy (BNil)))
let v45 () : ML blist = cons 0x1Buy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x00uy (cons 0x01uy (BNil))))))
let v46 () : ML blist = cons 0x63uy (cons 0xE1uy (cons 0xC0uy (cons 0x80uy (BNil))))
let v47 () : ML blist = cons 0x64uy (cons 0xF1uy (cons 0xC0uy (cons 0x80uy (cons 0x80uy (BNil)))))

(* [check] is split into groups of 32 rather than one long [main]: a
   single function with several hundred sequential statements roughly
   doubles this module's verification time. *)
let check (l : blist) (e : bool) (acc : ref bool) : ML unit =
  let r = validate l in
  if r <> e then acc := false

let g0 (ok : ref bool) : ML unit =
  check (v0 ()) true ok;
  check (v1 ()) true ok;
  check (v2 ()) true ok;
  check (v3 ()) true ok;
  check (v4 ()) true ok;
  check (v5 ()) true ok;
  check (v6 ()) true ok;
  check (v7 ()) true ok;
  check (v8 ()) true ok;
  check (v9 ()) true ok;
  check (v10 ()) true ok;
  check (v11 ()) true ok;
  check (v12 ()) true ok;
  check (v13 ()) true ok;
  check (v14 ()) true ok;
  check (v15 ()) true ok;
  check (v16 ()) true ok;
  check (v17 ()) true ok;
  check (v18 ()) true ok;
  check (v19 ()) true ok;
  check (v20 ()) true ok;
  check (v21 ()) true ok;
  check (v22 ()) true ok;
  check (v23 ()) true ok;
  check (v24 ()) true ok;
  check (v25 ()) true ok;
  check (v26 ()) false ok;
  check (v27 ()) false ok;
  check (v28 ()) false ok;
  check (v29 ()) false ok;
  check (v30 ()) false ok;
  check (v31 ()) false ok;
  ()

let g1 (ok : ref bool) : ML unit =
  check (v32 ()) false ok;
  check (v33 ()) false ok;
  check (v34 ()) false ok;
  check (v35 ()) false ok;
  check (v36 ()) false ok;
  check (v37 ()) false ok;
  check (v38 ()) false ok;
  check (v39 ()) false ok;
  check (v40 ()) false ok;
  check (v41 ()) false ok;
  check (v42 ()) false ok;
  check (v43 ()) false ok;
  check (v44 ()) false ok;
  check (v45 ()) false ok;
  check (v46 ()) false ok;
  check (v47 ()) false ok;
  ()

let main () : ML I32.t =
  let ok = alloc true in
  g0 ok;
  g1 ok;
  if !ok then 0l else 1l
