module LowParseWriters.NoHoare.Parsers
include LowParseWriters.Parsers
include LowParseWriters.NoHoare

module B = LowStar.Buffer
module U32 = FStar.UInt32

module P = LowParseWriters.Parsers
module LP = LowParse.Low.Base

inline_for_extraction
let deref
  (#p: parser)
  (#inv: memory_invariant)
  (r: LP.leaf_reader (get_parser p))
  (x: ptr p inv)
: TRead (y: Parser?.t p { y == deref_spec x }) inv
= tread_of_eread (fun _ -> let y = P.deref r x in (y <: (y: Parser?.t p { y == deref_spec x })))

inline_for_extraction
let access_t
  (p1 p2: parser)
  (#lens: LP.clens (Parser?.t p1) (Parser?.t p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
: Tot Type
=
  (#inv: memory_invariant) ->
  (x: ptr p1 inv {
    lens.LP.clens_cond (deref_spec x)
  }) ->
  TRead (y: ptr p2 inv {deref_spec y == lens.LP.clens_get (deref_spec x) }) inv

inline_for_extraction
let access
  (p1 p2: parser)
  (#lens: LP.clens (Parser?.t p1) (Parser?.t p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
: Tot (access_t p1 p2 a)
= fun #inv x ->
  tread_of_eread (fun _ -> let y = P.access p1 p2 a x in (y <: (y: ptr p2 inv {deref_spec y == lens.LP.clens_get (deref_spec x) })))

inline_for_extraction
let start
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: Parser?.t p)
: TWrite unit parse_empty (p) l
= twrite_of_ewrite (fun _ -> P.start p w x)

inline_for_extraction
let append
  (#fr: parser)
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: Parser?.t p)
: TWrite unit fr (fr `parse_pair` p) l
= twrite_of_ewrite (fun _ -> P.append p w x)

let valid_rewrite_parser_eq'
  (p1: parser)
  (p2: parser {
    Parser?.t p1 == Parser?.t p2 /\
    get_parser_kind p1 == get_parser_kind p2 /\
    get_parser p1 == LP.coerce (LP.parser (get_parser_kind p1) (Parser?.t p1)) (get_parser p2)
  })
: Tot (squash (valid_rewrite_prop p1 p2))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parser_eq p1 p2)

inline_for_extraction
let parse_vldata_intro_weak_ho'
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> TWrite unit parse_empty p inv))
: TWrite unit parse_empty (parse_vldata p min max)
    inv
=
  twrite_of_ewrite (fun _ -> parse_vldata_intro_weak_ho' p min max (fun _ -> ewrite_of_twrite f))

inline_for_extraction
let parse_vldata_recast
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: TWrite unit (parse_vldata p min max) (parse_vldata p min' max') inv
= twrite_of_ewrite (fun _ -> parse_vldata_recast p min max min' max')

inline_for_extraction
let destr_list'
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: ERead (y: option (ptr p inv & lptr p inv) {
    match y with
    | None -> deref_list_spec x == []
    | Some (hd, tl) -> deref_list_spec x == deref_spec hd :: deref_list_spec tl
  })
    True
    (fun _ -> True)
    (fun _ -> False)
    inv
=
  match destr_list x with
  | None -> None
  | Some (hd, tl) -> Some (hd, tl)

inline_for_extraction
let destr_list
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: TRead (y: option (ptr p inv & lptr p inv) {
    match y with
    | None -> deref_list_spec x == []
    | Some (hd, tl) -> deref_list_spec x == deref_spec hd :: deref_list_spec tl
  }) inv
= tread_of_eread (fun _ -> destr_list' x)

(*
let destr_list_is_correct
  (#p: parser1)
  (#inv: memory_invariant)
  (l: lptr p inv)
: Lemma
  (Correct? (ReadRepr?.spec (reify (destr_list l)) ()))
= assert_norm (Correct? (ReadRepr?.spec (reify (destr_list l)) ()))
*)

inline_for_extraction
let read_do_while
  (#inv: memory_invariant)
  (#t: Type0)
  (measure: (t -> GTot nat))
  (body: (
    (x: t) ->
    TRead
      (x'cond: (t & bool) {
        let (x', cond) = x'cond in
        cond == true ==> measure x' < measure x
      })
      inv
  ))
  (x: t)
: TRead
    t
    inv
= tread_of_eread (fun _ ->
    read_do_while
      #inv
      #t
      (fun _ _ -> True)
      measure
      (fun _ -> True)
      (fun x ->
        let (x', cond) = eread_of_tread (fun _ -> body x) in
        (x', cond)
      )
      x
  )

(* This will not extract.
let rec list_exists
  (#p: parser1)
  (#inv: memory_invariant)
  (f: ((x: ptr p inv) -> TRead bool inv))
  (l: lptr p inv)
: TRead bool inv
  (decreases (List.Tot.length (deref_list_spec l)))
= let x = destr_list l in
  match x with
  | None -> false
  | Some (hd, tl) ->
    let y = f hd in
    if y
    then true
    else list_exists f tl
*)

inline_for_extraction
let list_exists
  (#p: parser1)
  (#inv: memory_invariant)
  (f: ((x: ptr p inv) -> TRead bool inv))
  (l: lptr p inv)
: TRead bool inv
=
 let res = read_do_while
    #inv
    #(lptr p inv)
    (fun l1 -> List.Tot.length (deref_list_spec l1))
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
  match destr_list res with
  | None -> false
  | _ -> true

inline_for_extraction
let write_vllist_nil
  (#inv: memory_invariant)
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: TWrite unit parse_empty (parse_vllist p 0ul max) inv
= twrite_of_ewrite (fun _ -> parse_vllist_nil p max)

inline_for_extraction
let extend_vllist_snoc
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: TWrite unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max)
    inv
=
  twrite_of_ewrite (fun _ -> parse_vllist_snoc_weak p min max)

inline_for_extraction
let extend_vllist_snoc_ho
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> TWrite unit parse_empty p inv))
: TWrite unit (parse_vllist p min max) (parse_vllist p min max) inv
=
  twrite_of_ewrite (fun _ -> parse_vllist_snoc_weak_ho' p min max (fun _ -> ewrite_of_twrite f))

inline_for_extraction
let parse_vllist_recast
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: TWrite unit (parse_vllist p min max) (parse_vllist p min' max') inv
=
  twrite_of_ewrite (fun _ -> parse_vllist_recast p min max min' max')

inline_for_extraction
let get_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (p: ptr (parse_vlbytes min max) inv)
: TRead
    (B.buffer LP.byte & U32.t)
    inv
= 
  tread_of_eread (fun _ -> get_vlbytes min max p)

inline_for_extraction
let put_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
  (f: put_vlbytes_impl_t inv min max len l)
: TWrite unit parse_empty (parse_vlbytes min max) inv
= twrite_of_ewrite (fun _ -> put_vlbytes min max len l f)

inline_for_extraction
let do_while
  (#inv: memory_invariant)
  (#p: parser)
  (#t: Type0)
  (measure: (t -> GTot nat))
  (body: (
    (x: t) ->
    TWrite
      (x'cond: (t & bool) {
        let (x', cond) = x'cond in
        (cond == true ==>  measure x' < measure x)
      })
      p p
      inv
  ))
  (x: t)
: TWrite
    t p p
    inv
= twrite_of_ewrite (fun _ ->
    do_while
      #inv
      #p
      #t
      (fun _ _ _ -> True)
      (fun _ -> measure)
      (fun _ _ -> True)
      (fun x ->
        let (x', cond) = ewrite_of_twrite (fun _ -> body x) in
        (x', cond)
      )
      x
  )

(* This will not extract.
let rec list_map'
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f' : (
    (x: ptr p1 inv) ->
    TWrite unit parse_empty p2 inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: TWrite
    unit
    (parse_vllist p2 min max)
    (parse_vllist p2 min max)
    inv
  (decreases (deref_list_spec l))
=
  match destr_list l with
  | None -> ()
  | Some (hd, tl) ->
    frame (fun _ -> f' hd);
    parse_vllist_snoc_weak p2 min max;
    list_map' p1 p2 f' min max tl
*)

inline_for_extraction
let list_map'
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f' : (
    (x: ptr p1 inv) ->
    TWrite unit parse_empty p2 inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: TWrite
    unit
    (parse_vllist p2 min max)
    (parse_vllist p2 min max)
    inv
=
  let _ = do_while
    #inv
    #(parse_vllist p2 min max)
    #(lptr p1 inv)
    (fun l1 -> List.Tot.length (deref_list_spec l1))
    (fun l1 ->
      match destr_list l1 with
      | None ->
        (l1, false)
      | Some (hd, tl) ->
        frame (fun _ -> f' hd);
        extend_vllist_snoc p2 min max;
        (tl, true)
    )
    l
  in
  ()


inline_for_extraction
let list_map
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f' : (
    (x: ptr p1 inv) ->
    TWrite unit parse_empty p2 inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: TWrite unit parse_empty (parse_vllist p2 min max) inv
= write_vllist_nil p2 max;
  list_map' p1 p2 f' 0ul max l;
  parse_vllist_recast _ _ _ min max

(* Copy the contents of a list into a variable-sized list *)

inline_for_extraction
noextract
let cat_list
  (#p: parser1)
  (#inv: memory_invariant)
  (l: lptr p inv)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: TWrite unit parse_empty (parse_vllist p min max) inv
=
  list_map p p (fun x -> cat x) min max l
