module LowParseWriters.LowParse

module LP = LowParse.Low.Combinators
module LPI = LowParse.Low.Int
module U8 = FStar.UInt8
module Seq = FStar.Seq

noeq
inline_for_extraction
type parser'' t = {
  kind: (kind: LP.parser_kind { kind.LP.parser_kind_subkind == Some LP.ParserStrong }); // needed because of parse_pair; will be a problem with parse_list...
  parser: LP.parser kind t;
  serializer: LP.serializer parser;
  jumper: LP.jumper parser;
}

let parser' t = (parser'' t)

let slice_of_buffer
  (b: B.buffer U8.t)
: GTot (LP.slice _ _)
= LP.make_slice b (B.len b)

let valid_pos
  p h b pos pos'
= LP.valid_pos (Parser?.p p).parser h (slice_of_buffer b) pos pos'

let valid_pos_post
  p h b pos pos'
= ()

let contents
  p h b pos pos'
=
  LP.contents (Parser?.p p).parser h (slice_of_buffer b) pos

let size
  p x
= Seq.length (LP.serialize (Parser?.p p).serializer x)

let contents_size
  p h b pos pos'
= LP.valid_pos_valid_exact (Parser?.p p).parser h (slice_of_buffer b) pos pos';
  LP.valid_exact_serialize (Parser?.p p).serializer h (slice_of_buffer b) pos pos'

let parse_empty' = {
  kind = _;
  parser = LP.parse_empty;
  serializer = LP.serialize_empty;
  jumper = LP.jump_empty;
}

let valid_parse_empty
  h b pos pos'
=
  LP.valid_exact_equiv LP.parse_empty h (slice_of_buffer b) pos pos'

let size_parse_empty = ()

let parse_pair'
  #t1 #t2 p1 p2
= {
  kind = _;
  parser = LP.nondep_then p1.parser p2.parser;
  serializer = LP.serialize_nondep_then p1.serializer p2.serializer;
  jumper = LP.jump_nondep_then p1.jumper p2.jumper;
}

let valid_parse_pair
  p1 p2 h b pos1 pos2 pos3
=
  LP.valid_nondep_then h (Parser?.p p1).parser (Parser?.p p2).parser (slice_of_buffer b) pos1

let size_parse_pair
  p1 p2 x1 x2
=
  LP.length_serialize_nondep_then (Parser?.p p1).serializer (Parser?.p p2).serializer x1 x2

let valid_ext
  p h1 b1 pos1 pos1' h2 b2 pos2 pos2'
=
  assert (Seq.length (B.as_seq h2 (B.gsub b2 pos2 (pos2' `U32.sub` pos2))) == Seq.length (B.as_seq h1 (B.gsub b1 pos1 (pos1' `U32.sub` pos1))));
  assert (pos2' `U32.sub` pos2 == pos1' `U32.sub` pos1);
  LP.valid_ext_intro (Parser?.p p).parser h1 (LP.make_slice b1 (B.len b1)) pos1 h2 (LP.make_slice b2 (B.len b2)) pos2

let valid_parse_pair_inv_spec
  h p1 p2 b pos1 pos3
=
  let sl = LP.make_slice b (B.len b) in
  LP.valid_nondep_then h (Parser?.p p1).parser (Parser?.p p2).parser sl pos1;
  LP.get_valid_pos (Parser?.p p1).parser h sl pos1

let valid_parse_pair_inv
  p1 p2 b len pos1 pos3
=
  let h = HST.get () in
  LP.valid_nondep_then h (Parser?.p p1).parser (Parser?.p p2).parser (LP.make_slice b len) pos1;
  (Parser?.p p1).jumper (LP.make_slice b len) pos1

let clens_to_lp_clens
  (#t1 #t2: Type)
  (c: clens t1 t2)
: GTot (LP.clens t1 t2)
= {
  LP.clens_cond = c.clens_cond;
  LP.clens_get = c.clens_get
}

let gaccessor
  p1 p2 lens
= LP.gaccessor (Parser?.p p1).parser (Parser?.p p2).parser (clens_to_lp_clens lens)

#push-options "--z3rlimit 32"
#restart-solver

let gaccess
  #p1 #p2 #lens g h b
=
  let sl = LP.make_slice b (B.len b) in
  LP.valid_facts (Parser?.p p1).parser h sl 0ul;
  let posn = g (B.as_seq h b) in
  let pos = U32.uint_to_t posn in
  LP.valid_facts (Parser?.p p2).parser h sl pos;
  let pos' = LP.get_valid_pos (Parser?.p p2).parser h sl pos in
  let b1 = B.gsub b pos (B.len b `U32.sub` pos) in
  let len' = pos' `U32.sub` pos in
  let b' = B.gsub b1 0ul len' in
  LP.parse_strong_prefix (Parser?.p p2).parser (B.as_seq h b1) (B.as_seq h b');
  let sl' = LP.make_slice b' (B.len b') in
  LP.valid_facts (Parser?.p p2).parser h sl' 0ul;
  b'

let gaccessor_frame1
  (#p1 #p2: parser)
  (#lens: clens (Parser?.t p1) (Parser?.t p2))
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
      )
  )))
  (ensures (
    valid_buffer p1 h b /\
    valid_buffer p1 h' b /\
    buffer_contents p1 h b == buffer_contents p1 h' b /\
    lens.clens_cond (buffer_contents p1 h b) /\
    lens.clens_cond (buffer_contents p1 h' b) /\
    gaccess g h' b == gaccess g h b
  ))
= let sl = LP.make_slice b (B.len b) in
  LP.valid_facts (Parser?.p p1).parser h sl 0ul;
  let posn = g (B.as_seq h b) in
  let pos = U32.uint_to_t posn in
  LP.valid_facts (Parser?.p p2).parser h sl pos;
  let pos' = LP.get_valid_pos (Parser?.p p2).parser h sl pos in
  let b1 = B.gsub b pos (B.len b `U32.sub` pos) in
  let len' = pos' `U32.sub` pos in
  let b' = B.gsub b1 0ul len' in
  LP.parse_strong_prefix (Parser?.p p2).parser (B.as_seq h b1) (B.as_seq h b');
  let sl' = LP.make_slice b' (B.len b') in
  LP.valid_facts (Parser?.p p2).parser h sl' 0ul;
  ()

#pop-options

let gaccessor_frame
  #p1 #p2 #lens g h b l h'
=
  Classical.forall_intro (Classical.move_requires (gaccessor_frame1 g h b l))

let accessor
  #p1 #p2 #lens g
= LP.accessor g

#push-options "--z3rlimit 16"

let baccess
  #p1 #p2 #lens #g a b len
=
  let h = HST.get () in
  let sl = LP.make_slice b len in
  LP.valid_facts (Parser?.p p1).parser h sl 0ul;
  let pos = a sl 0ul in
  LP.slice_access_eq h g sl 0ul;
  LP.valid_facts (Parser?.p p2).parser h sl pos;
  let pos' = (Parser?.p p2).jumper sl pos in
  let b1 = B.sub b pos (B.len b `U32.sub` pos) in
  let len' = pos' `U32.sub` pos in
  let b' = B.sub b1 0ul len' in
  LP.parse_strong_prefix (Parser?.p p2).parser (B.as_seq h b1) (B.as_seq h b');
  LP.valid_facts (Parser?.p p2).parser h (LP.make_slice b' (B.len b')) 0ul;
  (b', len')

#pop-options

let validator
  p
=
  (
    squash begin match (Parser?.p p).kind.LP.parser_kind_high with
    | None -> False
    | Some max -> max <= U32.v LP.validator_max_length
    end &
    LP.validator (Parser?.p p).parser
  )

inline_for_extraction
let snd (a, b) = b

#push-options "--z3rlimit 16"

let gvalidate
  p h b
=
  let sl = LP.make_slice b (B.len b) in
  LP.valid_facts (Parser?.p p).parser h sl 0ul;
  match LP.parse (Parser?.p p).parser (B.as_seq h b) with
  | None -> None
  | Some (_, res) -> Some (U32.uint_to_t res)

#pop-options

let gvalidate_frame
  p h b l h'
=
  ()

let bvalidate
  #p v b len
=
  let res = LP.validate_bounded_strong_prefix (snd v) (LP.make_slice b len) 0ul in
  if res `U32.lte` LP.validator_max_length
  then Some res
  else None
