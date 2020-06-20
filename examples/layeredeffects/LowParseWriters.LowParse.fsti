module LowParseWriters.LowParse

module HS = FStar.HyperStack
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

inline_for_extraction
let dsnd
  (#u: Type)
  (#v: ((x: u) -> Type))
  (p: dtuple2 u v)
: Tot (v (dfst p))
= match p with (| _, x |) -> x

type u8 : Type0 = U8.t

val parser' (t: Type0) : Type0
let parser : Type u#1 = (t: Type0 & parser' t)

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
: Ghost (dfst p)
  (requires (valid_pos p h b pos pos'))
  (ensures (fun _ -> True))

val size
  (p: parser)
  (x: dfst p)
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

val emp' : parser' unit

let emp : parser = (| unit, emp' |)

val valid_emp
  (h: HS.mem)
  (b: B.buffer u8)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (
    valid_pos emp h b pos pos' <==> (
    B.live h b /\
    U32.v pos <= B.length b /\
    U32.v pos' == U32.v pos
  ))
  [SMTPat (valid_pos emp h b pos pos')]

val size_emp : squash (size emp () == 0)

val star' (#t1 #t2: Type) (p1: parser' t1) (p2: parser' t2) : Tot (parser' (t1 & t2))

let star (p1 p2: parser) : Tot parser = (| (dfst p1 & dfst p2), star' (dsnd p1) (dsnd p2) |)

val valid_star
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
    valid_pos (p1 `star` p2) h b pos1 pos3 /\
    contents (p1 `star` p2) h b pos1 pos3 == (contents p1 h b pos1 pos2, contents p2 h b pos2 pos3)
  ))

val size_star
  (p1 p2: parser)
  (x1: dfst p1)
  (x2: dfst p2)
: Lemma
  (size (p1 `star` p2) (x1, x2) == size p1 x1 + size p2 x2)
  [SMTPat (size (p1 `star` p2) (x1, x2))]

val valid_frame
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    valid_pos p h b pos pos' /\
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer_from_to b pos pos')
  ))
  (ensures (
    valid_pos p h b pos pos' /\
    valid_pos p h' b pos pos' /\
    contents p h' b pos pos' == contents p h b pos pos'
  ))

val valid_gsub_elim
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

val valid_gsub_intro
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

val parse_u32' : parser' U32.t

let parse_u32 : parser = (| U32.t , parse_u32' |)

inline_for_extraction
let leaf_writer
  (p: parser)
: Tot Type
=
  (b: B.buffer U8.t) ->
  (len: U32.t { len == B.len b }) ->
  (x: dfst p) ->
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

val write_u32 : leaf_writer parse_u32

inline_for_extraction
val valid_star_inv
  (p1 p2: parser)
  (b: B.buffer U8.t)
  (len: U32.t { len == B.len b })
  (pos1 pos3: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_pos (p1 `star` p2) h b pos1 pos3
  ))
  (ensures (fun h pos2 h' ->
    B.modifies B.loc_none h h' /\
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3 /\
    contents (p1 `star` p2) h b pos1 pos3 == (contents p1 h b pos1 pos2, contents p2 h b pos2 pos3)
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
: Ghost (dfst p)
  (requires (valid_buffer p h b))
  (ensures (fun _ -> True))
= contents p h b 0ul (B.len b)

inline_for_extraction
let leaf_reader
  (p: parser)
: Tot Type
=
  (b: B.buffer U8.t) ->
  HST.Stack (dfst p)
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

inline_for_extraction
let gaccessor
  (p1 p2: parser)
  (lens: clens (dfst p1) (dfst p2))
=
  (h: HS.mem) ->
  (b: B.buffer u8) ->
  Ghost (B.buffer u8)
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
  (#lens: clens (dfst p1) (dfst p2))
  (g: gaccessor p1 p2 lens)
  (h: HS.mem)
  (b: B.buffer u8)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
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
    g h' b == g h b
  ))

inline_for_extraction
let accessor
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (g: gaccessor p1 p2 lens)
=
  (b: B.buffer u8) ->
  HST.Stack (B.buffer u8)
  (requires (fun h ->
    valid_buffer p1 h b /\
    lens.clens_cond (buffer_contents p1 h b)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == g h b
  ))
