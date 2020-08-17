module LowParseWriters.Parsers
include LowParseWriters

module LP = LowParse.Low.Base
module LPI = LowParse.Spec.AllIntegers
module Seq = FStar.Seq
module U32 = FStar.UInt32

inline_for_extraction
noextract
val get_parser_kind
  (p: parser)
: Tot (kind: LP.parser_kind { kind.LP.parser_kind_subkind == Some LP.ParserStrong })

val get_parser
  (p: parser)
: Tot (LP.parser (get_parser_kind p) (Parser?.t p))

val get_serializer
  (p: parser)
: Tot (LP.serializer (get_parser p))

inline_for_extraction
noextract
val make_parser'
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Tot (parser' t)

inline_for_extraction
noextract
let make_parser
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Tot parser
= Parser t (make_parser' p s j)

val make_parser_correct
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Lemma
  (let p' = make_parser p s j in
   get_parser_kind p' == k /\
   get_parser p' == p /\
   get_serializer p' == s
  )
  [SMTPat (make_parser p s j)]

val size_correct
  (p: parser)
  (x: Parser?.t p)
: Lemma
  (size p x == Seq.length (LP.serialize (get_serializer p) x))
  [SMTPat (size p x)]

inline_for_extraction
val leaf_reader_of_lp_leaf_reader
  (p: parser)
  (r: LP.leaf_reader (get_parser p))
: Tot (leaf_reader p)

inline_for_extraction
let deref
  (#p: parser)
  (#inv: memory_invariant)
  (r: LP.leaf_reader (get_parser p))
  (x: ptr p inv)
: Read (Parser?.t p) True (fun res -> res == deref_spec x) inv
= deref (leaf_reader_of_lp_leaf_reader p r) x

inline_for_extraction
val leaf_writer_of_lp_leaf_writer
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
: Tot (leaf_writer p)

inline_for_extraction
let start
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: Parser?.t p)
: Write unit parse_empty (p) (fun _ -> True) (fun _ _ y -> y == x) l
= start (leaf_writer_of_lp_leaf_writer p w) x

inline_for_extraction
let append
  (#fr: parser)
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: Parser?.t p)
: Write unit fr (fr `parse_pair` p) (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x) l
= append (leaf_writer_of_lp_leaf_writer p w) x

inline_for_extraction
let access_t
  (p1 p2: parser)
  (#lens: LP.clens (Parser?.t p1) (Parser?.t p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
: Tot Type
=
  (#inv: memory_invariant) ->
  (x: ptr p1 inv) ->
  Read (ptr p2 inv) (lens.LP.clens_cond (deref_spec x)) (fun res -> lens.LP.clens_cond (deref_spec x) /\ deref_spec res == lens.LP.clens_get (deref_spec x)) inv

val access_spec
  (p1 p2: parser)
  (#lens: LP.clens (Parser?.t p1) (Parser?.t p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
  (#inv: memory_invariant)
  (x: ptr p1 inv)
: Ghost (ptr p2 inv)
  (requires (lens.LP.clens_cond (deref_spec x)))
  (ensures (fun res -> deref_spec res == lens.LP.clens_get (deref_spec x)))

inline_for_extraction
val access_impl
  (p1 p2: parser)
  (#lens: LP.clens (Parser?.t p1) (Parser?.t p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
  (#inv: memory_invariant)
  (x: ptr p1 inv)
: Tot (read_repr_impl _ (lens.LP.clens_cond (deref_spec x)) (fun res -> lens.LP.clens_cond (deref_spec x) /\ deref_spec res == lens.LP.clens_get (deref_spec x)) (fun _ -> False) inv (fun _ -> Correct (access_spec p1 p2 a x)))

inline_for_extraction
let access
  (p1 p2: parser)
  (#lens: LP.clens (Parser?.t p1) (Parser?.t p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
: Tot (access_t p1 p2 a)
= fun #inv x ->
  ERead?.reflect (ReadRepr _ (access_impl p1 p2 a x))

val valid_rewrite_parser_eq
  (p1: parser)
  (p2: parser {
    Parser?.t p1 == Parser?.t p2 /\
    get_parser_kind p1 == get_parser_kind p2 /\
    get_parser p1 == LP.coerce (LP.parser (get_parser_kind p1) (Parser?.t p1)) (get_parser p2)
  })
: Tot (valid_rewrite_t p1 p2 (fun _ -> True) (fun x -> x))

let parse_vldata_pred
  (min: nat)
  (max: nat)
  (p: parser)
  (x: Parser?.t p)
: GTot Type0
= let reslen = size p x in
  min <= reslen /\ reslen <= max

let parse_vldata_t
  (min: nat)
  (max: nat)
  (p: parser)
: Tot Type
= (x: Parser?.t p { parse_vldata_pred min max p x } )

inline_for_extraction
val parse_vldata
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (p' : parser {
    Parser?.t p' == parse_vldata_t (U32.v min) (U32.v max) p
  })

inline_for_extraction
let integer_size
: Type0
= (y: U32.t { 1 <= U32.v y /\ U32.v y <= 4 })

inline_for_extraction
let log256
  (max: U32.t { U32.v max > 0 })
: Tot integer_size
=
  if max `U32.lt` 256ul
  then 1ul
  else if max `U32.lt` 65536ul
  then 2ul
  else if max `U32.lt` 16777216ul
  then 3ul
  else 4ul

val size_parse_vldata
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (x: parse_vldata_t (U32.v min) (U32.v max) p)
: Lemma
  (U32.v (log256 max) + size p x == size (parse_vldata p min max) x)
  [SMTPat (size (parse_vldata p min max) x)]

val valid_rewrite_parse_vldata
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 })
: Tot (valid_rewrite_t (parse_vldata p min max) (parse_vldata p min' max') (fun x -> U32.v min' <= size p x /\ size p x <= U32.v max' /\ log256 max == log256 max')
(fun x -> x))

inline_for_extraction
val parse_bounded_integer
  (sz: integer_size)
: Tot (p' : parser {
    Parser?.t p' == LPI.bounded_integer (U32.v sz) /\
    get_parser_kind p' == LPI.parse_bounded_integer_kind (U32.v sz) /\
    get_parser p' == LPI.parse_bounded_integer (U32.v sz) /\
    get_serializer p' == LPI.serialize_bounded_integer (U32.v sz)
  })

let parse_vldata_intro_spec
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_bounded_integer (log256 max) `parse_pair` p) (parse_vldata p min max) (fun (_, vin) -> U32.v min <= size p vin /\ size p vin <= U32.v max) (fun (_, vin) _ vout -> vin == vout) (fun _ -> False))
=
  fun (_, vin) -> Correct ((), vin)

inline_for_extraction
val parse_vldata_intro_impl
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vldata_intro_spec p min max))

inline_for_extraction
let parse_vldata_intro
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Write unit (parse_bounded_integer (log256 max) `parse_pair` p) (parse_vldata p min max)
  (fun (_, vin) -> U32.v min <= size p vin /\ size p vin <= U32.v max)
  (fun (_, vin) _ vout -> vin == vout) inv
= EWrite?.reflect (Repr (parse_vldata_intro_spec p min max) (parse_vldata_intro_impl p min max))

inline_for_extraction
val write_bounded_integer
  (i: integer_size)
: Tot (LP.leaf_writer_strong (LPI.serialize_bounded_integer (U32.v i)))

inline_for_extraction
let parse_vldata_intro_ho
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (pre: pre_t parse_empty)
  (post: post_t unit parse_empty p pre)
  (post_err: post_err_t parse_empty pre)
  ($f: (unit -> EWrite unit parse_empty p pre post post_err inv))
: EWrite unit parse_empty (parse_vldata p min max)
    (fun _ ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v ==> (U32.v min <= size p v /\ size p v <= U32.v max)
      | _ -> True
      end
    )
    (fun _ _ vout ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\
        (vout <: Parser?.t p) == v
      | _ -> False
      end
    )
    (fun vin ->
      post_err ()
    )
    inv
=
  let int_size = log256 max in
  start (parse_bounded_integer int_size) (write_bounded_integer int_size) 0ul;
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vldata_intro _ _ _

inline_for_extraction
let parse_vldata_intro_ho'
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> EWrite unit parse_empty p (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: EWrite unit parse_empty (parse_vldata p min max)
    (fun _ ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        (U32.v min <= size p v /\ size p v <= U32.v max)
      | _ -> True
      end
    )
    (fun _ _ vout ->
      destr_repr_spec _ _ _ _ _ _ _ f () == Correct ((), vout)
    )
    (fun vin ->
      Error? (destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
=
  let int_size = log256 max in
  start (parse_bounded_integer int_size) (write_bounded_integer int_size) 0ul;
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vldata_intro _ _ _

inline_for_extraction
let parse_vldata_intro_frame
  (#inv: memory_invariant)
  (frame: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Write unit ((frame `parse_pair` parse_bounded_integer (log256 (max))) `parse_pair` p) (frame `parse_pair` parse_vldata p min max) (fun (_, vin) -> U32.v min <= size p vin /\ size p vin <= U32.v max) (fun ((fr, _), vin) _ (fr', vout) -> fr == fr' /\ (vin <: Parser?.t p) == (vout <: Parser?.t p)) inv
= valid_rewrite _ _ _ _ _ (valid_rewrite_parse_pair_assoc_1 _ _ _);
  frame2 _ _ _ _ _ _ _ _ (fun _ -> parse_vldata_intro p min max)

let parse_vldata_intro_weak_spec
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_bounded_integer (log256 (max)) `parse_pair` p) (parse_vldata p min max) (fun _ -> True) (fun (_, vin) _ vout -> vin == vout) (fun (_, vin) -> ~ (U32.v min <= size p vin /\ size p vin <= U32.v max)))
=
  fun (_, vin) ->
    let sz = size p vin in
    if U32.v min <= sz && sz <= U32.v max
    then Correct ((), vin)
    else Error "parse_vldata_intro_weak: out of bounds"

inline_for_extraction
val parse_vldata_intro_weak_impl
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vldata_intro_weak_spec p min max))

inline_for_extraction
let parse_vldata_intro_weak
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: EWrite unit (parse_bounded_integer (log256 (max)) `parse_pair` p) (parse_vldata p min max) (fun _ -> True) (fun (_, vin) _ vout -> vin == vout) (fun (_, vin) -> ~ (U32.v min <= size p vin /\ size p vin <= U32.v max)) inv
= EWrite?.reflect (Repr _ (parse_vldata_intro_weak_impl p min max))

inline_for_extraction
let parse_vldata_intro_weak_ho
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (pre: pre_t parse_empty)
  (post: post_t unit parse_empty p pre)
  (post_err: post_err_t parse_empty pre)
  ($f: (unit -> EWrite unit parse_empty p pre post post_err inv))
: EWrite unit parse_empty (parse_vldata p min max)
    (fun _ ->
      pre ()
    )
    (fun _ _ vout ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\
        (vout <: Parser?.t p) == v
      | _ -> False
      end
    )
    (fun vin ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\ (~ (U32.v min <= size p v /\ size p v <= U32.v max))
      | _ -> post_err ()
      end
    )
    inv
=
  let int_size = log256 max in
  start (parse_bounded_integer int_size) (write_bounded_integer int_size) 0ul;
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vldata_intro_weak _ _ _

inline_for_extraction
let parse_vldata_intro_weak_ho'
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> EWrite unit parse_empty p (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: EWrite unit parse_empty (parse_vldata p min max)
    (fun _ -> True)
    (fun _ _ vout ->
      destr_repr_spec _ _ _ _ _ _ _ f () == Correct ((), vout)
    )
    (fun vin ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        (~ (U32.v min <= size p v /\ size p v <= U32.v max))
      | _ -> True
      end
    )
    inv
=
  let int_size = log256 max in
  start (parse_bounded_integer int_size) (write_bounded_integer int_size) 0ul;
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vldata_intro_weak _ _ _

inline_for_extraction
let parse_vldata_intro_weak_frame
  (#inv: memory_invariant)
  (frame: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: EWrite unit ((frame `parse_pair` parse_bounded_integer (log256 (max))) `parse_pair` p) (frame `parse_pair` parse_vldata p min max) (fun _ -> True) (fun ((fr, _), vin) _ (fr', vout) -> fr == fr' /\ (vin <: Parser?.t p) == (vout <: Parser?.t p)) (fun (_, vin) -> ~ (U32.v min <= size p vin /\ size p vin <= U32.v max)) inv
= 
  valid_rewrite _ _ _ _ _ (valid_rewrite_parse_pair_assoc_1 _ _ _);
  frame2 _ _ _ _ _ _ _ _ (fun _ -> parse_vldata_intro_weak p min max)

let parse_vldata_recast_spec
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: Tot (repr_spec unit (parse_vldata p min max) (parse_vldata p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: Parser?.t p) == (vout <: Parser?.t p)) (fun vin -> ~ (U32.v min' <= size p vin /\ size p vin <= U32.v max')))
=
  fun vin ->
    let sz = size p vin in
    if U32.v min' <= sz && sz <= U32.v max'
    then Correct ((), vin)
    else Error "parse_vldata_recast: out of bounds"

inline_for_extraction
val parse_vldata_recast_impl
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vldata_recast_spec p min max min' max'))

inline_for_extraction
let parse_vldata_recast
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: EWrite unit (parse_vldata p min max) (parse_vldata p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: Parser?.t p) == (vout <: Parser?.t p)) (fun vin -> ~ (U32.v min' <= size p vin /\ size p vin <= U32.v max')) inv
= EWrite?.reflect (Repr _ (parse_vldata_recast_impl p min max min' max'))

inline_for_extraction
type parser1 = (p: parser {
  (get_parser_kind p).LP.parser_kind_low > 0
})

inline_for_extraction
val rlptr: Type0
val valid_rlptr (p: parser1) : memory_invariant -> rlptr -> GTot Type0

let lptr (p: parser1) (inv: memory_invariant) =
  (x: rlptr { valid_rlptr p inv x })

val deref_list_spec (#p: parser1) (#inv: memory_invariant) (x: lptr p inv) : GTot (list (Parser?.t p))

val valid_rlptr_frame
  (#p: parser1) (#inv: memory_invariant) (x: lptr p inv) (inv' : memory_invariant)
: Lemma
  (requires (
    inv `memory_invariant_includes` inv'
  ))
  (ensures (
    valid_rlptr p inv' x /\
    deref_list_spec #p #inv' x == deref_list_spec #p #inv x
  ))
  [SMTPatOr [
    [SMTPat (inv `memory_invariant_includes` inv'); SMTPat (valid_rlptr p inv x)];
    [SMTPat (inv `memory_invariant_includes` inv'); SMTPat (valid_rlptr p inv' x)];
  ]]

unfold
let destr_list_post
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
  (res: option (ptr p inv & lptr p inv))
: GTot Type0
= 
  match res, deref_list_spec x with
  | None, [] -> True
  | Some (hd, tl), hd' :: tl' ->
    deref_spec hd == hd' /\ deref_list_spec tl == tl'
  | _ -> False

inline_for_extraction
val destr_list_repr
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: Tot (read_repr (option (ptr p inv & lptr p inv)) (True) (destr_list_post x) (fun _ -> False) inv)

inline_for_extraction
let destr_list
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: Read (option (ptr p inv & lptr p inv)) (True) (destr_list_post x) inv
= ERead?.reflect (destr_list_repr x)

let rec read_do_while_spec'
  (inv: memory_invariant)
  (#t: Type0)
  (invariant: (t -> bool -> GTot Type0))
  (measure: (t -> GTot nat))
  (error: (t -> GTot Type0))
  (body: (
    (x: t) ->
    unit ->
    ERead
      (t & bool)
      (invariant x true)
      (fun (x', cond) ->
        invariant x true /\
        invariant x' cond /\
        (cond == true ==> measure x' < measure x)
      )
      (fun vin ->
        invariant x true /\
        error x
      )
      inv
  ))
  (x: t)
  ()
: Ghost (result t)
  (requires (
    invariant x true
  ))
  (ensures (fun res ->
    match res with
    | Error _ ->
      invariant x true /\
      (exists x' . invariant x' true /\ error x')
    | Correct x' ->
      invariant x true /\
      invariant x' false
  ))
  (decreases (measure x))
=
  match destr_read_repr_spec _ _ _ _ _ (body x) () with
  | Error e -> Error e
  | Correct (x', cond) ->
    if cond
    then read_do_while_spec' inv invariant measure error body x' ()
    else Correct x'

let read_do_while_spec
  (inv: memory_invariant)
  (#t: Type0)
  (invariant: (t -> bool -> GTot Type0))
  (measure: (t -> GTot nat))
  (error: t -> GTot Type0)
  (body: (
    (x: t) ->
    unit ->
    ERead
      (t & bool)
      (invariant x true)
      (fun (x', cond) ->
        invariant x true /\
        invariant x' cond /\
        (cond == true ==> measure x' < measure x)
      )
      (fun _ ->
        invariant x true /\
        error x
      )
      inv
  ))
  (x: t)
: Tot (read_repr_spec t
    (invariant x true)
    (fun x' ->
      invariant x true /\
      invariant x' false
    )
    (fun _ ->
      invariant x true /\
      (exists x' . invariant x' true /\ error x')
    )
  )
=
  fun vin -> read_do_while_spec' inv invariant measure error body x vin

inline_for_extraction
val read_do_while_impl
  (inv: memory_invariant)
  (#t: Type0)
  (invariant: (t -> bool -> GTot Type0))
  (measure: (t -> GTot nat))
  (error: t -> GTot Type0)
  (body: (
    (x: t) ->
    unit ->
    ERead
      (t & bool)
      (invariant x true)
      (fun (x', cond) ->
        invariant x true /\
        invariant x' cond /\
        (cond == true ==> measure x' < measure x)
      )
      (fun _ ->
        invariant x true /\
        error x
      )
      inv
  ))
  (x: t)
: Tot (read_repr_impl _ _ _ _ inv (read_do_while_spec inv invariant measure error body x))

inline_for_extraction
let read_do_while'
  (#inv: memory_invariant)
  (#t: Type0)
  (invariant: (t -> bool -> GTot Type0))
  (measure: (t -> GTot nat))
  (error: t -> GTot Type0)
  (body: (
    (x: t) ->
    unit ->
    ERead
      (t & bool)
      (invariant x true)
      (fun (x', cond) ->
        invariant x true /\
        invariant x' cond /\
        (cond == true ==> measure x' < measure x)
      )
      (fun _ ->
        invariant x true /\
        error x
      )
      inv
  ))
  (x: t)
: ERead
    t
    (invariant x true)
    (fun x' ->
      invariant x true /\
      invariant x' false
    )
    (fun _ ->
      invariant x true /\
      (exists x' . invariant x' true /\ error x')
    )
    inv
= ERead?.reflect (
    ReadRepr
      (read_do_while_spec inv invariant measure error body x)
      (read_do_while_impl inv invariant measure error body x)
  )

inline_for_extraction
let read_do_while
  (#inv: memory_invariant)
  (#t: Type0)
  (invariant: (t -> bool -> GTot Type0))
  (measure: (t -> GTot nat))
  (error: t -> GTot Type0)
  (body: (
    (x: t) ->
    ERead
      (t & bool)
      (invariant x true)
      (fun (x', cond) ->
        invariant x true /\
        invariant x' cond /\
        (cond == true ==> measure x' < measure x)
      )
      (fun _ ->
        invariant x true /\
        error x
      )
      inv
  ))
  (x: t)
: ERead
    t
    (invariant x true)
    (fun x' ->
      invariant x true /\
      invariant x' false
    )
    (fun _ ->
      invariant x true /\
      (exists x' . invariant x' true /\ error x')
    )
    inv
= read_do_while' invariant measure error (fun x _ -> body x) x


(* This will not extract.
let rec list_exists
  (#p: parser1)
  (#inv: memory_invariant)
  (f_spec: Ghost.erased (Parser?.t p -> Tot bool)) // reifying f below is not enough because of the ptr
  (f: ((x: ptr p inv) -> Read bool (True) (fun res -> res == Ghost.reveal f_spec (deref_spec x)) inv))
  (l: lptr p inv)
: Read bool (True) (fun res -> res == List.Tot.existsb f_spec (deref_list_spec l)) inv
  (decreases (List.Tot.length (deref_list_spec l)))
= match destr_list l with
  | None -> false
  | Some (hd, tl) ->
    if f hd
    then true
    else list_exists f_spec f tl
*)

inline_for_extraction
let list_exists
  (#p: parser1)
  (#inv: memory_invariant)
  (f_spec: Ghost.erased (Parser?.t p -> Tot bool)) // reifying f below is not enough because of the ptr
  (f: ((x: ptr p inv) -> Read bool (True) (fun res -> res == Ghost.reveal f_spec (deref_spec x)) inv))
  (l: lptr p inv)
: Read bool (True) (fun res -> res == List.Tot.existsb f_spec (deref_list_spec l)) inv
  (decreases (List.Tot.length (deref_list_spec l)))
= let res = read_do_while
    #inv
    #(lptr p inv)
    (fun l1 continue ->
        List.Tot.existsb f_spec (deref_list_spec l) ==
        (if continue then List.Tot.existsb f_spec (deref_list_spec l1) else Cons? (deref_list_spec l1))
    )
    (fun l1 -> List.Tot.length (deref_list_spec l1))
    (fun _ -> False)
    (fun l1 ->
      match destr_list l1 with
      | None -> (l1, false)
      | Some (hd, tl) ->
        if f hd
        then (l1, false)
        else (tl, true)
    )
    l
  in
  Some? (destr_list res)

val list_size
  (p: parser1)
  (x: list (Parser?.t p))
: GTot nat

val list_size_nil
  (p: parser1)
: Lemma
  (list_size p [] == 0)
  [SMTPat (list_size p [])]

val list_size_cons
  (p: parser1)
  (a: Parser?.t p)
  (q: list (Parser?.t p))
: Lemma
  (list_size p (a :: q) == size p a + list_size p q)
  [SMTPat (list_size p (a :: q))]

module L = FStar.List.Tot

let rec list_size_append
  (p: parser1)
  (l1 l2: list (Parser?.t p))
: Lemma
  (list_size p (l1 `L.append` l2) == list_size p l1 + list_size p l2)
  [SMTPat (list_size p (l1 `L.append` l2))]
= match l1 with
  | [] -> ()
  | a :: q -> list_size_append p q l2

let parse_vllist_pred
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (x: list (Parser?.t p))
: GTot Type0
= let s = list_size p x in
  U32.v min <= s /\ s <= U32.v max

let parse_vllist_t
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot Type
= (x: list (Parser?.t p) { parse_vllist_pred p min max x })

inline_for_extraction
val parse_vllist
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (p' : parser {
    Parser?.t p' == parse_vllist_t p min max
  })

val parse_vllist_size
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (x: parse_vllist_t p min max)
: Lemma
  (size (parse_vllist p min max) x == U32.v (log256 max) + list_size p x)
  [SMTPat (size (parse_vllist p min max) x)]

inline_for_extraction
val lptr_of_vllist_ptr_repr
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (r: ptr (parse_vllist p min max) inv)
: Tot (read_repr (lptr p inv) True (fun r' -> deref_list_spec r' == (deref_spec r <: list (Parser?.t p))) (fun _ -> False) inv)

inline_for_extraction
let lptr_of_vllist_ptr
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (r: ptr (parse_vllist p min max) inv)
: Read (lptr p inv) True (fun r' -> deref_list_spec r' == (deref_spec r <: list (Parser?.t p))) inv
= ERead?.reflect (lptr_of_vllist_ptr_repr p min max r)

let parse_vllist_nil_spec
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: Tot (repr_spec unit parse_empty (parse_vllist p 0ul max) (fun _ -> True) (fun _ _ x -> (x <: list (Parser?.t p)) == [] /\ list_size p x == 0) (fun _ -> False))
= fun _ ->
  Correct ((), ([] <: parse_vllist_t p 0ul max))

inline_for_extraction
val parse_vllist_nil_impl
  (#inv: memory_invariant)
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_nil_spec p max))

inline_for_extraction
let parse_vllist_nil
  (#inv: memory_invariant)
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: Write unit parse_empty (parse_vllist p 0ul max) (fun _ -> True) (fun _ _ x -> (x <: list (Parser?.t p)) == [] /\ list_size p x == 0) inv
= EWrite?.reflect (Repr _ (parse_vllist_nil_impl p max))

let parse_vllist_snoc_spec
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      U32.v min <= sz /\ sz <= U32.v max)
    (fun (l, x) _ l' -> (l' <: list (Parser?.t p)) == L.snoc ((l <: list (Parser?.t p)), x) /\ list_size p l' == list_size p l + size p x)
    (fun _ -> False)
  )
= fun (l, x) ->
  Correct ((), L.snoc ((l <: list (Parser?.t p)), x))

inline_for_extraction
val parse_vllist_snoc_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_snoc_spec p min max))

inline_for_extraction
let parse_vllist_snoc
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Write unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      U32.v min <= sz /\ sz <= U32.v max)
    (fun (l, x) _ l' -> (l' <: list (Parser?.t p)) == L.snoc ((l <: list (Parser?.t p)), x) /\ list_size p l' == list_size p l + size p x)
    inv
=
  EWrite?.reflect (Repr _ (parse_vllist_snoc_impl p min max))

inline_for_extraction
let parse_vllist_snoc_ho
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (pre: pre_t parse_empty)
  (post: post_t unit parse_empty p pre)
  (post_err: post_err_t parse_empty pre)
  ($f: (unit -> EWrite unit parse_empty p pre post post_err inv))
: EWrite unit (parse_vllist p min max) (parse_vllist p min max)
    (fun vin ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v ==> list_size p vin + size p v <= U32.v max
      | _ -> True
      end
    )
    (fun vin _ vout ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\
        (vout <: list (Parser?.t p)) == (vin <: list (Parser?.t p)) `L.append` [v]
      | _ -> False
      end
    )
    (fun vin ->
      post_err ()
    )
    inv
=
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vllist_snoc _ _ _

inline_for_extraction
let parse_vllist_snoc_ho'
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> EWrite unit parse_empty p (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: EWrite unit (parse_vllist p min max) (parse_vllist p min max)
    (fun vin ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        list_size p vin + size p v <= U32.v max
      | _ -> True
      end
    )
    (fun vin _ vout ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        (vout <: list (Parser?.t p)) == (vin <: list (Parser?.t p)) `L.append` [v]
      | _ -> False
      end
    )
    (fun vin ->
      Error? (destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
=
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vllist_snoc _ _ _

let parse_vllist_snoc_weak_spec
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max)
    (fun _ -> True)
    (fun (l, x) _ l' -> (l' <: list (Parser?.t p)) == L.snoc ((l <: list (Parser?.t p)), x) /\ list_size p l' == list_size p l + size p x)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      ~ (U32.v min <= sz /\ sz <= U32.v max))
  )
= fun (l, x) ->
  let sz = list_size p l + size p x in
  if U32.v min <= sz && sz <= U32.v max
  then begin
    Correct ((), L.snoc ((l <: list (Parser?.t p)), x))
  end else
    Error "parse_vllist_snoc_weak: out of bounds"

inline_for_extraction
val parse_vllist_snoc_weak_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_snoc_weak_spec p min max))

inline_for_extraction
let parse_vllist_snoc_weak
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: EWrite unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max)
    (fun _ -> True)
    (fun (l, x) _ l' -> (l' <: list (Parser?.t p)) == L.snoc ((l <: list (Parser?.t p)), x) /\ list_size p l' == list_size p l + size p x)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      ~ (U32.v min <= sz /\ sz <= U32.v max))
    inv
=
  EWrite?.reflect (Repr _ (parse_vllist_snoc_weak_impl p min max))

inline_for_extraction
let parse_vllist_snoc_weak_ho
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (pre: pre_t parse_empty)
  (post: post_t unit parse_empty p pre)
  (post_err: post_err_t parse_empty pre)
  ($f: (unit -> EWrite unit parse_empty p pre post post_err inv))
: EWrite unit (parse_vllist p min max) (parse_vllist p min max)
    (fun vin ->
      pre ()
    )
    (fun vin _ vout ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\
        (vout <: list (Parser?.t p)) == (vin <: list (Parser?.t p)) `L.append` [v]
      | _ -> False
      end
    )
    (fun vin ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\
        list_size p vin + size p v > U32.v max
      | _ -> post_err ()
      end
    )
    inv
=
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vllist_snoc_weak _ _ _

inline_for_extraction
let parse_vllist_snoc_weak_ho'
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> EWrite unit parse_empty p (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: EWrite unit (parse_vllist p min max) (parse_vllist p min max)
    (fun vin -> True)
    (fun vin _ vout ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        (vout <: list (Parser?.t p)) == (vin <: list (Parser?.t p)) `L.append` [v]
      | _ -> False
      end
    )
    (fun vin ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        list_size p vin + size p v > U32.v max
      | _ -> True
      end
    )
    inv
=
  frame _ _ _ _ _ _ _ (fun _ -> recast_writer _ _ _ _ _ _ _ f);
  parse_vllist_snoc_weak _ _ _

val valid_rewrite_parse_vllist
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 })
: Tot (valid_rewrite_t (parse_vllist p min max) (parse_vllist p min' max') (fun x -> U32.v min' <= list_size p x /\ list_size p x <= U32.v max' /\ log256 (max) == log256 (max'))
(fun x -> x))

let parse_vllist_recast_spec
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 max == log256 (max')})
: Tot (repr_spec unit (parse_vllist p min max) (parse_vllist p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: list (Parser?.t p)) == (vout <: list (Parser?.t p))) (fun vin -> ~ (U32.v min' <= list_size p vin /\ list_size p vin <= U32.v max')))
=
  fun vin ->
    let sz = list_size p vin in
    if U32.v min' <= sz && sz <= U32.v max'
    then Correct ((), vin)
    else Error "parse_vllist_recast: out of bounds"

inline_for_extraction
val parse_vllist_recast_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 max'})
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_recast_spec p min max min' max'))

inline_for_extraction
let parse_vllist_recast
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: EWrite unit (parse_vllist p min max) (parse_vllist p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: list (Parser?.t p)) == (vout <: list (Parser?.t p))) (fun vin -> ~ (U32.v min' <= list_size p vin /\ list_size p vin <= U32.v max')) inv
= EWrite?.reflect (Repr _ (parse_vllist_recast_impl p min max min' max'))

let parse_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: FStar.Bytes.bytes)
: GTot Type0
= let reslen = FStar.Bytes.length x in
  min <= reslen /\ reslen <= max

let parse_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type
= (x: FStar.Bytes.bytes { parse_vlbytes_pred min max x } )

inline_for_extraction
val parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (p' : parser {
    Parser?.t p' == parse_vlbytes_t (U32.v min) (U32.v max)
  })

module B = LowStar.Buffer

val get_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (p: ptr (parse_vlbytes min max) inv)
: Read
    (B.buffer LP.byte & U32.t)
    True
    (fun (b, len) ->
      B.live inv.h0 b /\
      len == B.len b /\
      B.as_seq inv.h0 b `Seq.equal` FStar.Bytes.reveal (deref_spec p)
    )
    inv

let put_vlbytes_spec
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: Ghost.erased (Seq.seq LP.byte) { U32.v min <= Seq.length l /\ Seq.length l <= U32.v max })
: Tot (repr_spec unit parse_empty (parse_vlbytes min max) (fun _ -> True) (fun _ _ vout -> vout == FStar.Bytes.hide (Ghost.reveal l)) (fun _ -> False))
=
  fun _ -> Correct ((), FStar.Bytes.hide (Ghost.reveal l))

module HST = FStar.HyperStack.ST

inline_for_extraction
let put_vlbytes_impl_t
  (inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
: Tot Type
=
    (b: B.buffer LP.byte) ->
    HST.Stack unit
    (requires (fun h ->
      B.modifies inv.lwrite inv.h0 h /\
      B.live h b /\
      B.len b == len /\
      inv.lwrite `B.loc_includes` B.loc_buffer b
    ))
    (ensures (fun h _ h' ->
      B.modifies (B.loc_buffer b) h h' /\
      B.as_seq h' b `Seq.equal` Ghost.reveal l
    ))

inline_for_extraction
val put_vlbytes_impl
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
  (f: put_vlbytes_impl_t inv min max len l)
: Tot (repr_impl _ _ _ _ _ _ inv (put_vlbytes_spec min max l))

inline_for_extraction
let put_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
  (f: put_vlbytes_impl_t inv min max len l)
: Write unit parse_empty (parse_vlbytes min max) (fun _ -> True) (fun _ _ vout -> vout == FStar.Bytes.hide (Ghost.reveal l)) inv
= EWrite?.reflect (Repr _ (put_vlbytes_impl min max len l f))

let rec do_while_spec'
  (inv: memory_invariant)
  (#p: parser)
  (#t: Type0)
  (invariant: (Parser?.t p -> t -> bool -> GTot Type0))
  (measure: (Parser?.t p -> t -> GTot nat))
  (error: (Parser?.t p -> t -> GTot Type0))
  (body: (
    (x: t) ->
    unit ->
    EWrite
      (t & bool) p p
      (fun vin -> invariant vin x true)
      (fun vin (x', cond) vout ->
        invariant vin x true /\
        invariant vout x' cond /\
        (cond == true ==> measure vout x' < measure vin x)
      )
      (fun vin ->
        invariant vin x true /\
        error vin x
      )
      inv
  ))
  (x: t)
  (vin: Parser?.t p)
: Ghost (result (t & Parser?.t p))
  (requires (
    invariant vin x true
  ))
  (ensures (fun res ->
    match res with
    | Error _ ->
      invariant vin x true /\
      (exists vout x' . invariant vout x' true /\ error vout x')
    | Correct (x', vout) ->
      invariant vin x true /\
      invariant vout x' false /\
      size p vout >= size p vin
  ))
  (decreases (measure vin x))
=
  match destr_repr_spec _ _ _ _ _ _ _ (body x) vin with
  | Error e -> Error e
  | Correct ((x', cond), vout) ->
    if cond
    then do_while_spec' inv invariant measure error body x' vout
    else Correct (x', vout)

let do_while_spec
  (inv: memory_invariant)
  (#p: parser)
  (#t: Type0)
  (invariant: (Parser?.t p -> t -> bool -> GTot Type0))
  (measure: (Parser?.t p -> t -> GTot nat))
  (error: Parser?.t p -> t -> GTot Type0)
  (body: (
    (x: t) ->
    unit ->
    EWrite
      (t & bool) p p
      (fun vin -> invariant vin x true)
      (fun vin (x', cond) vout ->
        invariant vin x true /\
        invariant vout x' cond /\
        (cond == true ==> measure vout x' < measure vin x)
      )
      (fun vin ->
        invariant vin x true /\
        error vin x
      )
      inv
  ))
  (x: t)
: Tot (repr_spec t p p
    (fun vin -> invariant vin x true)
    (fun vin x' vout ->
      invariant vin x true /\
      invariant vout x' false
    )
    (fun vin ->
      invariant vin x true /\
      (exists vout x' . invariant vout x' true /\ error vout x')
    )
  )
=
  fun vin -> do_while_spec' inv invariant measure error body x vin

inline_for_extraction
val do_while_impl
  (inv: memory_invariant)
  (#p: parser)
  (#t: Type0)
  (invariant: (Parser?.t p -> t -> bool -> GTot Type0))
  (measure: (Parser?.t p -> t -> GTot nat))
  (error: Parser?.t p -> t -> GTot Type0)
  (body: (
    (x: t) ->
    unit ->
    EWrite
      (t & bool) p p
      (fun vin -> invariant vin x true)
      (fun vin (x', cond) vout ->
        invariant vin x true /\
        invariant vout x' cond /\
        (cond == true ==> measure vout x' < measure vin x)
      )
      (fun vin ->
        invariant vin x true /\
        error vin x
      )
      inv
  ))
  (x: t)
: Tot (repr_impl _ _ _ _ _ _ inv (do_while_spec inv invariant measure error body x))

inline_for_extraction
let do_while'
  (#inv: memory_invariant)
  (#p: parser)
  (#t: Type0)
  (invariant: (Parser?.t p -> t -> bool -> GTot Type0))
  (measure: (Parser?.t p -> t -> GTot nat))
  (error: Parser?.t p -> t -> GTot Type0)
  (body: (
    (x: t) ->
    unit ->
    EWrite
      (t & bool) p p
      (fun vin -> invariant vin x true)
      (fun vin (x', cond) vout ->
        invariant vin x true /\
        invariant vout x' cond /\
        (cond == true ==> measure vout x' < measure vin x)
      )
      (fun vin ->
        invariant vin x true /\
        error vin x
      )
      inv
  ))
  (x: t)
: EWrite
    t p p
    (fun vin -> invariant vin x true)
    (fun vin x' vout ->
      invariant vin x true /\
      invariant vout x' false
    )
    (fun vin ->
      invariant vin x true /\
      (exists vout x' . invariant vout x' true /\ error vout x')
    )
    inv
= EWrite?.reflect (
    Repr
      (do_while_spec inv invariant measure error (body) x)
      (do_while_impl inv invariant measure error (body) x)
  )

inline_for_extraction
let do_while
  (#inv: memory_invariant)
  (#p: parser)
  (#t: Type0)
  (invariant: (Parser?.t p -> t -> bool -> GTot Type0))
  (measure: (Parser?.t p -> t -> GTot nat))
  (error: Parser?.t p -> t -> GTot Type0)
  (body: (
    (x: t) ->
    EWrite
      (t & bool) p p
      (fun vin -> invariant vin x true)
      (fun vin (x', cond) vout ->
        invariant vin x true /\
        invariant vout x' cond /\
        (cond == true ==> measure vout x' < measure vin x)
      )
      (fun vin ->
        invariant vin x true /\
        error vin x
      )
      inv
  ))
  (x: t)
: EWrite
    t p p
    (fun vin -> invariant vin x true)
    (fun vin x' vout ->
      invariant vin x true /\
      invariant vout x' false
    )
    (fun vin ->
      invariant vin x true /\
      (exists vout x' . invariant vout x' true /\ error vout x')
    )
    inv
= do_while' invariant measure error (fun x _ -> body x) x


(* // This will not extract.
let rec list_map'
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f: Ghost.erased (Parser?.t p1 -> Tot (Parser?.t p2)))
  (f' : (
    (x: ptr p1 inv) ->
    Write unit parse_empty p2 (fun _ -> True) (fun _ _ out -> out == Ghost.reveal f (deref_spec x)) inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: EWrite
    unit
    (parse_vllist p2 min max)
    (parse_vllist p2 min max)
    (fun _ -> True)
    (fun lin _ lout -> (lout <: list (Parser?.t p2)) == (lin <: list (Parser?.t p2)) `L.append` L.map (Ghost.reveal f) (deref_list_spec l))
    (fun lin -> list_size p2 lin + list_size p2 (L.map (Ghost.reveal f) (deref_list_spec l)) > U32.v max)
    inv
  (decreases (deref_list_spec l))
=
  let lin = get_state () in
  match destr_list l with
  | None ->
    L.append_l_nil (Ghost.reveal lin <: list (Parser?.t p2))
  | Some (hd, tl) ->
    frame _ _ _ _ _ _ _ (fun _ -> f' hd);
    parse_vllist_snoc_weak p2 min max;
    L.append_assoc (Ghost.reveal lin) [Ghost.reveal f (deref_spec hd)] (L.map (Ghost.reveal f) (deref_list_spec tl));
    list_map' p1 p2 f f' min max tl
*)

#push-options "--z3rlimit 16"

inline_for_extraction
let list_map'
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f: Ghost.erased (Parser?.t p1 -> Tot (Parser?.t p2)))
  (f' : (
    (x: ptr p1 inv) ->
    Write unit parse_empty p2 (fun _ -> True) (fun _ _ out -> out == Ghost.reveal f (deref_spec x)) inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: EWrite
    unit
    (parse_vllist p2 min max)
    (parse_vllist p2 min max)
    (fun _ -> True)
    (fun lin _ lout -> (lout <: list (Parser?.t p2)) == (lin <: list (Parser?.t p2)) `L.append` L.map (Ghost.reveal f) (deref_list_spec l))
    (fun lin -> list_size p2 lin + list_size p2 (L.map (Ghost.reveal f) (deref_list_spec l)) > U32.v max)
    inv
=
  let lin0 = get_state () in
  let _ = do_while
    #inv
    #(parse_vllist p2 min max)
    #(lptr p1 inv)
    (fun lin l1 cond ->
      lin0 `L.append` L.map (Ghost.reveal f) (deref_list_spec l) ==
      lin  `L.append` L.map (Ghost.reveal f) (deref_list_spec l1) /\
      (cond == false ==> deref_list_spec l1 == [])
    )
    (fun _ l1 -> L.length (deref_list_spec l1))
    (fun lin l1 ->
      list_size p2 lin + list_size p2 (L.map (Ghost.reveal f) (deref_list_spec l1)) > U32.v max
    )
    (fun l1 ->
      let lin = get_state () in
      match destr_list l1 with
      | None ->
        (l1, false)
      | Some (hd, tl) ->
        L.append_assoc (Ghost.reveal lin) [Ghost.reveal f (deref_spec hd)] (L.map (Ghost.reveal f) (deref_list_spec tl));
        frame _ _ _ _ _ _ _ (fun _ -> f' hd);
        parse_vllist_snoc_weak p2 min max;
        (tl, true)
    )
    l
  in
  let lin = get_state () in
  L.append_l_nil (Ghost.reveal lin <: list (Parser?.t p2));
  ()

#pop-options

inline_for_extraction
let list_map
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f: Ghost.erased (Parser?.t p1 -> Tot (Parser?.t p2)))
  (f' : (
    (x: ptr p1 inv) ->
    Write unit parse_empty p2 (fun _ -> True) (fun _ _ out -> out == Ghost.reveal f (deref_spec x)) inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: EWrite
    unit
    parse_empty
    (parse_vllist p2 min max)
    (fun _ -> True)
    (fun _ _ lout -> (lout <: list (Parser?.t p2)) == L.map (Ghost.reveal f) (deref_list_spec l))
    (fun _ -> let len = list_size p2 (L.map (Ghost.reveal f) (deref_list_spec l)) in len < U32.v min \/ len > U32.v max)
    inv
=
  parse_vllist_nil p2 max;
  list_map' p1 p2 f f' 0ul max l;
  parse_vllist_recast p2 0ul max min max

(* integers *)

inline_for_extraction
noextract
val parse_u32 : (p': parser {
  Parser?.t p' == U32.t /\
  get_parser_kind p' == LPI.parse_u32_kind /\
  get_parser p' == LPI.parse_u32 /\
  get_serializer p' == LPI.serialize_u32
})

inline_for_extraction
noextract
val parse_u16 : (p': parser {
  Parser?.t p' == FStar.UInt16.t /\
  get_parser_kind p' == LPI.parse_u16_kind /\
  get_parser p' == LPI.parse_u16 /\
  get_serializer p' == LPI.serialize_u16
})

inline_for_extraction
noextract
val parse_u8 : (p': parser {
  Parser?.t p' == FStar.UInt8.t /\
  get_parser_kind p' == LPI.parse_u8_kind /\
  get_parser p' == LPI.parse_u8 /\
  get_serializer p' == LPI.serialize_u8
})
