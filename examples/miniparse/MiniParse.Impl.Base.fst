module MiniParse.Impl.Base
include MiniParse.Spec.Base

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

inline_for_extraction
let buffer8 = B.buffer U8.t

inline_for_extraction
let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) -> (l: U32.t { l == B.len input } ) -> HST.Stack (option (t * U32.t))
  (requires (fun h -> B.live h input))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\ (
    match parse p (B.as_seq h input), res with
    | None, None -> True
    | Some (y, consumed), Some (y', consumed') -> y == y' /\ U32.v consumed' == consumed
    | _ -> False
  )))

inline_for_extraction
let coerce_parser32
  (t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (#p: parser k t1)
  (p32: parser32 p)
  (u: unit { t2 == t1 } )
: Tot (parser32 (coerce_parser t2 p))
= p32

inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (output: buffer8) -> (l: U32.t { l == B.len output } ) -> (x: t) -> HST.Stack (option U32.t)
  (requires (fun h -> B.live h output))
  (ensures (fun h res h' ->
    B.live h output /\ B.live h' output /\ (
    let len = Seq.length (serialize s x) in
    match res with
    | None ->
      M.modifies (M.loc_buffer output) h h' /\ len > B.length output
    | Some len' ->
      U32.v len' == len /\
      len <= B.length output /\ (
      let b' = B.gsub output 0ul len' in
      M.modifies (M.loc_buffer b') h h' /\
      B.as_seq h' b' == serialize s x
    ))))
