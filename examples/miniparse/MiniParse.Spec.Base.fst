module MiniParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

inline_for_extraction
type byte = U8.t
type bytes = Seq.seq byte

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type now forbids lookahead; the parser cannot depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure

[@"substitute"]
inline_for_extraction
let consumed_length (b: bytes) : Tot Type0 = (n: nat { n <= Seq.length b } )

inline_for_extraction
let bare_parser (t:Type0) : Tot Type0 = (b: bytes) -> GTot (option (t * consumed_length b))

let bparse
  (#t: Type0)
  (p: bare_parser t)
  (input: bytes)
: GTot (option (t * consumed_length input))
= p input

let no_lookahead_weak_on
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= Some? (bparse f x) ==> (
  let (Some v) = bparse f x in
  let (y, off) = v in (
  (off <= Seq.length x' /\ Seq.length x' <= Seq.length x /\ Seq.slice x' 0 off == Seq.slice x 0 off) ==>
  Some? (bparse f x') /\ (
  let (Some v') = bparse f x' in
  let (y', off') = v' in
  y == y' /\ (off <: nat) == (off' <: nat)
  )))

let no_lookahead_weak_on_ext
  (#t: Type0)
  (f1 f2: bare_parser t)
  (x x' : bytes)
: Lemma
  (requires (
    bparse f2 x == bparse f1 x /\
    bparse f2 x' == bparse f1 x'
  ))
  (ensures (
    no_lookahead_weak_on f2 x x' <==> no_lookahead_weak_on f1 x x'
  ))
= ()

let no_lookahead_weak
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes) . no_lookahead_weak_on f x x'

let no_lookahead_weak_ext
  (#t: Type0)
  (f1 f2: bare_parser t)
: Lemma
  (requires (
    (forall (b: bytes) . bparse f2 b == bparse f1 b)
  ))
  (ensures (
    no_lookahead_weak f2 <==> no_lookahead_weak f1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_weak_on_ext f1 f2 b1))

(** Injectivity of parsing *)

let injective_precond
  (#t: Type0)
  (p: bare_parser t)
  (b1 b2: bytes)
: GTot Type0
= Some? (bparse p b1) /\
  Some? (bparse p b2) /\ (
    let (Some (v1, len1)) = bparse p b1 in
    let (Some (v2, len2)) = bparse p b2 in
    v1 == v2
  )

let injective_precond_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    bparse p2 b1 == bparse p1 b1 /\
    bparse p2 b2 == bparse p1 b2
  ))
  (ensures (
    injective_precond p2 b1 b2 <==> injective_precond p1 b1 b2
  ))
= ()

let injective_postcond
  (#t: Type0)
  (p: bare_parser t)
  (b1 b2: bytes)
: GTot Type0
= Some? (bparse p b1) /\
  Some? (bparse p b2) /\ (
    let (Some (v1, len1)) = bparse p b1 in
    let (Some (v2, len2)) = bparse p b2 in
    (len1 <: nat) == (len2 <: nat) /\
    Seq.slice b1 0 len1 == Seq.slice b2 0 len2
  )

let injective_postcond_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    bparse p2 b1 == bparse p1 b1 /\
    bparse p2 b2 == bparse p1 b2
  ))
  (ensures (
    injective_postcond p2 b1 b2 <==> injective_postcond p1 b1 b2
  ))
= ()

let injective (#t: Type0) (p: bare_parser t) : GTot Type0 =
  forall (b1 b2: bytes) .
  injective_precond p b1 b2 ==>
  injective_postcond p b1 b2

let injective_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes) . bparse p2 b == bparse p1 b
  ))
  (ensures (
    injective p2 <==> injective p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_precond_ext p1 p2 b1));
  Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_postcond_ext p1 p2 b1))
  
let no_lookahead_on_precond
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= Some? (bparse f x) /\ (
    let (Some v) = bparse f x in
    let (_, off) = v in
    off <= Seq.length x' /\
    Seq.slice x' 0 off == Seq.slice x 0 off
  )

let no_lookahead_on_postcond
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= Some? (bparse f x) ==> (
  let (Some v) = bparse f x in
  let (y, _) = v in
  Some? (bparse f x') /\ (
  let (Some v') = bparse f x' in
  let (y', _) = v' in
  y == y'
  ))

let no_lookahead_on
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= no_lookahead_on_precond f x x' ==> no_lookahead_on_postcond f x x'

let no_lookahead_on_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    bparse p2 b1 == bparse p1 b1 /\
    bparse p2 b2 == bparse p1 b2
  ))
  (ensures (
    no_lookahead_on p2 b1 b2 <==> no_lookahead_on p1 b1 b2
  ))
= ()

let no_lookahead
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes) . no_lookahead_on f x x'

let no_lookahead_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes) . bparse p2 b == bparse p1 b
  ))
  (ensures (
    no_lookahead p2 <==> no_lookahead p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_on_ext p1 p2 b1))

noeq
type parser_spec
  (t: Type0)
= | Parser : (f: bare_parser t {
    no_lookahead_weak f /\
    injective f /\
    no_lookahead f
  } ) -> parser_spec t

(* AR: see bug#1349 *)
unfold let coerce_to_bare_parser (t:Type0) (p:parser_spec t)
  :Tot (bare_parser t) = Parser?.f p

let parse
  (#t: Type0)
  (p: parser_spec t)
  (input: bytes)
: GTot (option (t * consumed_length input))
= bparse (coerce_to_bare_parser _ p) input

(* Coercions *)

unfold
let coerce
  (t2: Type)
  (#t1: Type)
  (x: t1)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun _ -> True))
= (x <: t2)

unfold
let coerce_parser
  (t2: Type0)
  (#t1: Type0)
  (p: parser_spec t1)
: Pure (parser_spec t2)
  (requires (t2 == t1))
  (ensures (fun _ -> True))
= p

(* Pure serializers *)

inline_for_extraction
let bare_serializer
  (t: Type0)
: Tot Type0
= t -> GTot bytes

let serializer_correct
  (#t: Type0)
  (p: parser_spec t)
  (f: bare_serializer t)
: GTot Type0
= forall (x: t) . parse p (f x) == Some (x, Seq.length (f x))

let serializer_correct_ext
  (#t1: Type0)
  (p1: parser_spec t1)
  (f: bare_serializer t1)
  (#t2: Type0)
  (p2: parser_spec t2)
: Lemma
  (requires (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
  (ensures (serializer_correct p1 f <==> serializer_correct p2 f))
= ()

let serializer_complete
  (#t: Type0)
  (p: parser_spec t)
  (f: bare_serializer t)
: GTot Type0
= forall (s: bytes) .
  Some? (parse p s) ==> (
    let (Some (x, len)) = parse p s in
    f x == Seq.slice s 0 len
  )

let serializer_correct_implies_complete
  (#t: Type0)
  (p: parser_spec t)
  (f: bare_serializer t)
: Lemma
  (requires (serializer_correct p f))
  (ensures (serializer_complete p f))
= let prf
    (s: bytes)
  : Lemma
    (requires (Some? (parse p s)))
    (ensures (
      Some? (parse p s) /\ (
      let (Some (x, len)) = parse p s in
      f x == Seq.slice s 0 len
    )))
  = let (Some (x, len)) = parse p s in
    assert (no_lookahead_weak_on (coerce_to_bare_parser _ p) (f x) s);
    assert (injective_precond (coerce_to_bare_parser _ p) (f x) s);
    assert (injective_postcond (coerce_to_bare_parser _ p) (f x) s)
  in
  Classical.forall_intro (Classical.move_requires prf)

noeq
type serializer_spec
  (#t: Type0)
  (p: parser_spec t)
= | Serializer : (f: bare_serializer t { serializer_correct p f } ) -> serializer_spec p

unfold
let coerce_serializer
  (t2: Type0)
  (#t1: Type0)
  (#p: parser_spec t1)
  (s: serializer_spec p)
  (u: unit { t2 == t1 } )
: Tot (serializer_spec (coerce_parser t2 p))
= s

let serialize_ext
  (#t1: Type0)
  (p1: parser_spec t1)
  (s1: serializer_spec p1)
  (#t2: Type0)
  (p2: parser_spec t2)
: Pure (serializer_spec p2)
  (requires (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
  (ensures (fun _ -> True))
= serializer_correct_ext p1 (Serializer?.f s1) p2;
  Serializer (Serializer?.f s1 <: bare_serializer t2)

let serialize_ext'
  (#t1: Type0)
  (p1: parser_spec t1)
  (s1: serializer_spec p1)
  (#t2: Type0)
  (p2: parser_spec t2)
: Pure (serializer_spec p2)
  (requires (t1 == t2 /\ p1 == p2))
  (ensures (fun _ -> True))
= serialize_ext p1 s1 p2

let serialize
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (x: t)
: GTot bytes
= Serializer?.f s x

let serializer_unique
  (#t: Type0)
  (p: parser_spec t)
  (s1 s2: serializer_spec p)
  (x: t)
: Lemma
  (serialize s1 x == serialize s2 x)
= serializer_correct_implies_complete p (Serializer?.f s2)

let serializer_injective
  (#t: Type0)
  (p: parser_spec t)
  (s: serializer_spec p)
  (x1 x2: t)
: Lemma
  (requires (serialize s x1 == serialize s x2))
  (ensures (x1 == x2))
= ()

let serializer_parser_unique'
  (#t: Type0)
  (p1: parser_spec t)
  (p2: parser_spec t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    serializer_correct p1 s /\
    serializer_correct p2 s /\
    Some? (parse p1 x)
  ))
  (ensures (
    parse p1 x == parse p2 x
  ))
= serializer_correct_implies_complete p1 s;
  let (Some (y, len)) = parse p1 x in
  let x' = Seq.slice x 0 len in
  assert (s y == x');
  let len' = Seq.length x' in
  assert (len == len');
  assert (parse p1 x' == Some (y, len'));
  assert (parse p2 x' == Some (y, len'));
  assert (no_lookahead_on (coerce_to_bare_parser _ p2) x' x);
  assert (no_lookahead_on_postcond (coerce_to_bare_parser _ p2) x' x);
  assert (injective_postcond (coerce_to_bare_parser _ p2) x' x)

let serializer_parser_unique
  (#t: Type0)
  (p1: parser_spec t)
  (p2: parser_spec t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    serializer_correct p1 s /\
    serializer_correct p2 s
  ))
  (ensures (
    parse p1 x == parse p2 x
  ))
= if Some? (parse p1 x)
  then serializer_parser_unique' p1 p2 s x
  else if Some? (parse p2 x)
  then serializer_parser_unique' p2 p1 s x
  else ()
