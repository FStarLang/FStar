module MiniParse.Impl.Combinators
include MiniParse.Impl.Base
include MiniParse.Spec.Combinators

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

inline_for_extraction
let parse32_ret
  (#t: Type)
  (x: t)
: Tot (parser32 (parse_ret x))
= fun _ _ -> let h = HST.get () in Some (x, 0ul)

inline_for_extraction
let parse32_and_then
  (#t:Type)
  (#p:parser t)
  (p32: parser32 p)
  (#t':Type)
  (p': (t -> Tot (parser t')))
  (u: unit { and_then_cases_injective p' } )
  (p32' : ((x: t) -> Tot (parser32 (p' x))))
: Tot (parser32 (p `and_then` p'))
= fun (input: buffer8) (len: U32.t { len == B.len input } ) ->
  match p32 input len with
  | Some (v, l) ->
    let input' = B.offset input l in
    begin match p32' v input' (len `U32.sub` l) with
    | Some (v', l') ->
      Some (v', U32.add l l')
    | _ -> None
    end
  | _ -> None

#set-options "--z3rlimit 16"

inline_for_extraction
let parse32_nondep_then
  (#t1: Type0)
  (#p1: parser t1)
  (p1' : parser32 p1)
  (#t2: Type0)
  (#p2: parser t2)
  (p2' : parser32 p2)
: Tot (parser32 (nondep_then p1 p2))
= parse32_and_then p1' _ () (fun x -> parse32_and_then p2' _ () (fun y -> parse32_ret (x, y)))

let seq_append_slice
  (#t: Type)
  (s: Seq.seq t)
  (i1 i2: nat)
: Lemma
  (requires (i1 + i2 <= Seq.length s))
  (ensures (
    Seq.append (Seq.slice s 0 i1) (Seq.slice s i1 (i1 + i2)) == Seq.slice s 0 (i1 + i2)
  ))
= assert (Seq.append (Seq.slice s 0 i1) (Seq.slice s i1 (i1 + i2)) `Seq.equal` Seq.slice s 0 (i1 + i2))

inline_for_extraction
let serialize32_nondep_then
  (#t1: Type0)
  (#p1: parser t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1)
  (#t2: Type0)
  (#p2: parser t2)
  (#s2: serializer p2)
  (s2' : serializer32 s2)
: Tot (serializer32 (serialize_nondep_then s1 s2))
= fun (output: buffer8) (l: U32.t { l == B.len output } ) (input: t1 * t2) ->
  match input with
  | (fs, sn) ->
    begin match s1' output l fs with
    | Some l1 ->
      let h1 = HST.get () in
      let output' = B.offset output l1 in
      begin match s2' output' (l `U32.sub` l1) sn with
      | Some l2 ->
        let h2 = HST.get () in
        assert (B.as_seq h1 (B.gsub output 0ul l1) == B.as_seq h2 (B.gsub output 0ul l1));
        seq_append_slice (B.as_seq h2 output) (U32.v l1) (U32.v l2);
        assert (Seq.append (B.as_seq h2 (B.gsub output 0ul l1)) (B.as_seq h2 (B.gsub output' 0ul l2)) `Seq.equal` B.as_seq h2 (B.gsub output 0ul (l1 `U32.add` l2)));
        Some (l1 `U32.add` l2)
      | _ -> None
      end
    | _ -> None
    end

inline_for_extraction
let parse32_synth
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser t1)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : parser32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (parser32 (parse_synth p1 f2))
= fun (input: buffer8) (len: U32.t { len == B.len input } ) ->
    match p1' input len with
    | Some (v1, consumed) -> Some ((f2' v1 <: t2), consumed)
    | _ -> None

inline_for_extraction
let serialize32_synth
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (g1: t2 -> GTot t1)
  (g1': (x: t2) -> Tot (y: t1 { y == g1 x } ) )
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer32 (serialize_synth p1 f2 s1 g1 u))
= fun (output: buffer8) (len: U32.t { len == B.len output } ) (input: t2) ->
    let x = g1' input in
    s1' output len x

inline_for_extraction
let parse32_filter
  (#t: Type0)
  (#p: parser t)
  (p32: parser32 p)
  (f: (t -> GTot bool))
  (g: ((x: t) -> Tot (b: bool { b == f x } )))
: Tot (parser32 (parse_filter p f))
= fun (input: buffer8) (len: U32.t { len == B.len input } ) ->
    match p32 input len with
    | Some (v, consumed) ->
      if g v
      then
        [@inline_let]
        let (v' : t { f v' == true } ) = v in
	Some (v', consumed)
      else
        None
    | _ -> None

inline_for_extraction
let serialize32_filter
  (#t: Type0)
  (#p: parser t)
  (#s: serializer p)
  (s32: serializer32 s)
  (f: (t -> GTot bool))
: Tot (serializer32 (serialize_filter s f))
= fun (output: buffer8) (len: U32.t { len == B.len output } ) (input: t { f input == true } ) -> s32 output len input

inline_for_extraction
let make_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
  (u: unit {
    make_constant_size_parser_precond sz t f
  } )
  (f' : (
    (s: buffer8 { B.length s == sz } ) ->
    HST.Stack (option t)
    (requires (fun h -> B.live h s))
    (ensures (fun h y h' ->
      M.modifies M.loc_none h h' /\
      y == f (B.as_seq h s)
  ))))
: Tot (parser32 (make_constant_size_parser sz t f))
= fun (input: buffer8) (len: U32.t { len == B.len input } ) ->
    if U32.lt len sz'
    then None
    else begin
      let s' = B.sub input 0ul sz' in
      match f' s' with
      | None -> None
      | Some v -> Some (v, (sz' <: U32.t))
    end

inline_for_extraction
let make_total_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (t)))
  (u: unit {
    make_total_constant_size_parser_precond sz t f
  })
  (f' : (
    (s: buffer8 { B.length s == sz } ) ->
    HST.Stack t
    (requires (fun h -> B.live h s))
    (ensures (fun h y h' ->
      M.modifies M.loc_none h h' /\
      y == f (B.as_seq h s)
  ))))
: Tot (parser32 (make_total_constant_size_parser sz t f))
= fun (input: buffer8) (len: U32.t { len == B.len input } ) ->
    if U32.lt len sz'
    then None
    else
      let s' = B.sub input 0ul sz' in
      Some (f' s', (sz' <: U32.t))
