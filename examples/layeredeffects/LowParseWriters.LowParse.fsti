module LowParseWriters.LowParse

module HS = FStar.HyperStack
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

type u8 : Type0 = U8.t

val parser' (t: Type0) : Type u#1

inline_for_extraction
noextract
noeq
type parser =
| Parser:
  t: Type ->
  p: parser' t ->
  parser

val valid_pos
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0

val valid_pos_post
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h b pos pos'))
  (ensures (
    B.live h b /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= B.length b
  ))
  [SMTPat (valid_pos p h b pos pos')]

val contents
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost (Parser?.t p)
  (requires (valid_pos p h b pos pos'))
  (ensures (fun _ -> True))

val size
  (p: parser)
  (x: Parser?.t p)
: GTot nat

val contents_size
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h b pos pos'))
  (ensures (
    valid_pos p h b pos pos' /\
    size p (contents p h b pos pos') == U32.v pos' - U32.v pos
  ))
  [SMTPat (contents p h b pos pos')]

inline_for_extraction
val parse_empty' : parser' unit

inline_for_extraction
let parse_empty : parser = Parser unit parse_empty'

val valid_parse_empty
  (h: HS.mem)
  (b: B.buffer u8)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (
    valid_pos parse_empty h b pos pos' <==> (
    B.live h b /\
    U32.v pos <= B.length b /\
    U32.v pos' == U32.v pos
  ))
  [SMTPat (valid_pos parse_empty h b pos pos')]

val size_parse_empty : squash (size parse_empty () == 0)

inline_for_extraction
val parse_pair' (#t1 #t2: Type) (p1: parser' t1) (p2: parser' t2) : Tot (parser' (t1 & t2))

inline_for_extraction
let parse_pair (p1 p2: parser) : Tot parser = Parser (Parser?.t p1 & Parser?.t p2) (parse_pair' (Parser?.p p1) (Parser?.p p2))

val valid_parse_pair
  (p1 p2: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos1 pos2 pos3: U32.t)
: Lemma
  (requires (
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3
  ))
  (ensures (
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3 /\
    valid_pos (p1 `parse_pair` p2) h b pos1 pos3 /\
    contents (p1 `parse_pair` p2) h b pos1 pos3 == (contents p1 h b pos1 pos2, contents p2 h b pos2 pos3)
  ))

val size_parse_pair
  (p1 p2: parser)
  (x1: Parser?.t p1)
  (x2: Parser?.t p2)
: Lemma
  (size (p1 `parse_pair` p2) (x1, x2) == size p1 x1 + size p2 x2)
  [SMTPat (size (p1 `parse_pair` p2) (x1, x2))]

val valid_ext
  (p: parser)
  (h1: HS.mem)
  (b1: B.buffer U8.t)
  (pos1: U32.t)
  (pos1' : U32.t)
  (h2: HS.mem)
  (b2: B.buffer U8.t)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_pos p h1 b1 pos1 pos1' /\
    U32.v pos2 <= U32.v pos2' /\
    U32.v pos2' <= B.length b2 /\
    B.live h2 b2 /\
    B.as_seq h2 (B.gsub b2 pos2 (pos2' `U32.sub` pos2)) `Seq.equal` B.as_seq h1 (B.gsub b1 pos1 (pos1' `U32.sub` pos1))
  ))
  (ensures (
    valid_pos p h1 b1 pos1 pos1' /\
    valid_pos p h2 b2 pos2 pos2' /\
    contents p h2 b2 pos2 pos2' == contents p h1 b1 pos1 pos1'
  ))

let valid_frame
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    B.live h b /\
    (valid_pos p h b pos pos' \/ valid_pos p h' b pos pos') /\
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer_from_to b pos pos')
  ))
  (ensures (
    valid_pos p h b pos pos' /\
    valid_pos p h' b pos pos' /\
    contents p h' b pos pos' == contents p h b pos pos'
  ))
= B.loc_buffer_mgsub_eq (B.trivial_preorder _) b pos (pos' `U32.sub` pos);
  Classical.move_requires (valid_ext p h b pos pos' h' b pos) pos';
  Classical.move_requires (valid_ext p h' b pos pos' h b pos) pos'

let valid_gsub_elim
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos0 pos1 pos2: U32.t)
  (len: U32.t)
: Lemma
  (requires (
    U32.v pos0 + U32.v len <= B.length b /\
    valid_pos p h (B.gsub b pos0 len) pos1 pos2 /\
    B.live h b
  ))
  (ensures (
    U32.v pos0 + U32.v pos2 <= B.length b /\
    valid_pos p h (B.gsub b pos0 len) pos1 pos2 /\
    valid_pos p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2) /\
    contents p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2) == contents p h (B.gsub b pos0 len) pos1 pos2
  ))
  [SMTPat (valid_pos p h (B.gsub b pos0 len) pos1 pos2)]
=
  valid_ext p h (B.gsub b pos0 len) pos1 pos2 h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2)

let valid_gsub_intro
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos0 pos1 pos2: U32.t)
  (len: U32.t)
: Lemma
  (requires (
    U32.v pos0 + U32.v len <= B.length b /\
    U32.v pos1 <= U32.v pos2 /\
    U32.v pos2 <= U32.v len /\
    valid_pos p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2)
  ))
  (ensures (
    valid_pos p h (B.gsub b pos0 len) pos1 pos2 /\
    contents p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2) == contents p h (B.gsub b pos0 len) pos1 pos2
  ))
  [SMTPat (valid_pos p h (B.gsub b pos0 len) pos1 pos2)]
=
  valid_ext p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2) h (B.gsub b pos0 len) pos1 pos2

inline_for_extraction
let leaf_writer
  (p: parser)
: Tot Type
=
  (b: B.buffer U8.t) ->
  (len: U32.t { len == B.len b }) ->
  (x: Parser?.t p) ->
  HST.Stack (option U32.t)
  (requires (fun h -> B.live h b))
  (ensures (fun h res h' ->
    match res with
    | None ->
      B.modifies (B.loc_buffer b) h h' /\
      size p x > B.length b
    | Some xlen ->
      U32.v xlen <= B.length b /\
      B.modifies (B.loc_buffer_from_to b 0ul xlen) h h' /\
      valid_pos p h' b 0ul xlen /\
      contents p h' b 0ul xlen == x /\
      size p x == U32.v xlen
  ))  

val valid_parse_pair_inv_spec
  (h: HS.mem)
  (p1 p2: parser)
  (b: B.buffer U8.t)
  (pos1 pos3: U32.t)
: Ghost U32.t
  (requires (
    valid_pos (p1 `parse_pair` p2) h b pos1 pos3
  ))
  (ensures (fun pos2 ->
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3 /\
    contents (p1 `parse_pair` p2) h b pos1 pos3 == (contents p1 h b pos1 pos2, contents p2 h b pos2 pos3)
  ))

inline_for_extraction
val valid_parse_pair_inv
  (p1 p2: parser)
  (b: B.buffer U8.t)
  (len: U32.t { len == B.len b })
  (pos1 pos3: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_pos (p1 `parse_pair` p2) h b pos1 pos3
  ))
  (ensures (fun h pos2 h' ->
    B.modifies B.loc_none h h' /\
    pos2 == valid_parse_pair_inv_spec h p1 p2 b pos1 pos3 /\
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3 /\
    contents (p1 `parse_pair` p2) h b pos1 pos3 == (contents p1 h b pos1 pos2, contents p2 h b pos2 pos3)
  ))

let valid_buffer
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
: GTot Type0
= valid_pos p h b 0ul (B.len b)

let buffer_contents
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
: Ghost (Parser?.t p)
  (requires (valid_buffer p h b))
  (ensures (fun _ -> True))
= contents p h b 0ul (B.len b)

inline_for_extraction
let leaf_reader
  (p: parser)
: Tot Type
=
  (b: B.buffer U8.t) ->
  (len: U32.t { B.len b == len }) ->
  HST.Stack (Parser?.t p)
  (requires (fun h ->
    valid_buffer p h b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == buffer_contents p h b
  ))  

noeq
type clens (t1: Type) (t2: Type) = {
  clens_cond: t1 -> GTot Type0;
  clens_get: (x1: t1) -> Ghost t2 (requires (clens_cond x1)) (ensures (fun _ -> True));
}

val gaccessor
  (p1 p2: parser)
  (lens: clens (Parser?.t p1) (Parser?.t p2))
: Tot Type0

inline_for_extraction
val gaccess
  (#p1 #p2: parser)
  (#lens: clens (Parser?.t p1) (Parser?.t p2))
  (g: gaccessor p1 p2 lens)
  (h: HS.mem)
  (b: B.buffer u8)
: Ghost (B.buffer u8)
  (requires (
    valid_buffer p1 h b /\
    lens.clens_cond (buffer_contents p1 h b)
  ))
  (ensures (fun b' ->
    B.loc_buffer b `B.loc_includes` B.loc_buffer b' /\
    valid_buffer p2 h b' /\
    buffer_contents p2 h b' == lens.clens_get (buffer_contents p1 h b)
  ))

inline_for_extraction
val gaccessor_frame
  (#p1 #p2: parser)
  (#lens: clens (Parser?.t p1) (Parser?.t p2))
  (g: gaccessor p1 p2 lens)
  (h: HS.mem)
  (b: B.buffer u8)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    B.live h b /\
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer b) /\ (
      (
        valid_buffer p1 h b /\
        lens.clens_cond (buffer_contents p1 h b)
      ) \/ (
        valid_buffer p1 h' b /\
        lens.clens_cond (buffer_contents p1 h' b)
  ))))
  (ensures (
    valid_buffer p1 h b /\
    valid_buffer p1 h' b /\
    buffer_contents p1 h b == buffer_contents p1 h' b /\
    lens.clens_cond (buffer_contents p1 h b) /\
    lens.clens_cond (buffer_contents p1 h' b) /\
    gaccess g h' b == gaccess g h b
  ))

inline_for_extraction
val accessor
  (#p1 #p2: parser)
  (#lens: clens (Parser?.t p1) (Parser?.t p2))
  (g: gaccessor p1 p2 lens)
: Tot (Type u#1)

inline_for_extraction
val baccess
  (#p1 #p2: parser)
  (#lens: clens (Parser?.t p1) (Parser?.t p2))
  (#g: gaccessor p1 p2 lens)
  (a: accessor g)
  (b: B.buffer u8)
  (len: U32.t { B.len b == len })
: HST.Stack (B.buffer u8 & U32.t)
  (requires (fun h ->
    valid_buffer p1 h b /\
    lens.clens_cond (buffer_contents p1 h b)
  ))
  (ensures (fun h (res, res_len) h' ->
    B.modifies B.loc_none h h' /\
    res == gaccess g h b /\
    res_len == B.len res
  ))

inline_for_extraction
val validator
  (p: parser)
: Tot (Type u#1)

val gvalidate
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
: Ghost (option U32.t)
  (requires (B.live h b))
  (ensures (fun res ->
    match res with
    | None -> forall pos . ~ (valid_pos p h b 0ul pos)
    | Some pos -> valid_pos p h b 0ul pos
  ))

val gvalidate_frame
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    B.live h b /\
    l `B.loc_disjoint` B.loc_buffer b /\
    B.modifies l h h'
  ))
  (ensures (
    gvalidate p h b == gvalidate p h' b
  ))

inline_for_extraction
val bvalidate
  (#p: parser)
  (v: validator p)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: HST.Stack (option U32.t)
  (requires (fun h -> B.live h b))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == gvalidate p h b
  ))
