module MiniParse.Impl.List
include MiniParse.Spec.List
include MiniParse.Impl.Base

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module BO = LowStar.BufferOps
module M = LowStar.ModifiesPat
module CL = C.Loops
module L = FStar.List.Tot

let parse_nlist_impl_inv_easy
  (#t: Type0)
  (n: nat)
  (h0: HS.mem)
  (b: buffer8)
  (rb: B.pointer (x: U32.t { U32.v x <= B.length b } ))
  (rr: B.pointer (list t))
  (h: HS.mem)
  (i: nat)
  (stop: bool)
: Tot Type0
= M.loc_disjoint (M.loc_buffer rb) (M.loc_buffer rr) /\
  M.loc_disjoint (M.loc_buffer b) (M.loc_union (M.loc_buffer rb) (M.loc_buffer rr)) /\
  M.modifies (M.loc_union (M.loc_buffer rb) (M.loc_buffer rr)) h0 h /\
  i <= n /\
  B.live h0 b /\ B.live h b /\ B.live h rb /\ B.live h rr

let parse_nlist_impl_inv
  (#t: Type0)
  (p0: parser_spec t)
  (n: nat)
  (h0: HS.mem)
  (b: buffer8)
  (rb: B.pointer (x: U32.t { U32.v x <= B.length b } ))
  (rr: B.pointer (list t))
  (h: HS.mem)
  (i: nat)
  (stop: bool)
: Tot Type0
= parse_nlist_impl_inv_easy n h0 b rb rr h i stop /\ (
  let off = BO.deref h rb in
  let b' = B.gsub b off (B.len b `U32.sub` off) in
  let p = parse (parse_nlist n p0) (B.as_seq h0 b) in
  let p' = parse (parse_nlist (n - i) p0) (B.as_seq h0 b') in
  if stop
  then None? p
  else match p, p' with
  | Some (l, consumed), Some (l', consumed') ->
    consumed == U32.v off + consumed' /\
    l == L.append (L.rev (BO.deref h rr)) l'
  | None, None -> True
  | _ -> False
  )

let list_assoc_append (#t: Type) (x: t) (l1 l2: list t) : Lemma
  (L.append (L.rev l1) (x :: l2) == L.append (L.rev (x :: l1)) l2)
= L.append_assoc (L.rev l1) [x] l2;
  L.rev_append [x] l1

#set-options "--z3rlimit 64 --max_ifuel 8"

let parse_nlist_impl_inv_false_intro
  (#t: Type0)
  (p0: parser_spec t)
  (n: nat)
  (h0: HS.mem)
  (b: buffer8)
  (rb: B.pointer (x: U32.t { U32.v x <= B.length b } ))
  (rr: B.pointer (list t))
  (h1 h2: HS.mem)
  (i: nat { i < n } )
  (off : U32.t)
  (off' : U32.t)
  (b' : buffer8)
  (b'_after : buffer8)
  (l: nlist n t)
  (elem: t)
  (consumed1: nat)
  (consumed: nat)
  (l'_before: nlist (n - i) t)
  (consumed_before : nat)
  (l'_after: nlist (n - (i + 1)) t)
  (consumed_after: nat)
: Lemma
  (requires (
    parse_nlist_impl_inv p0 n h0 b rb rr h1 (i) false /\
    parse_nlist_impl_inv_easy n h0 b rb rr h2 (i + 1) false /\
    off == BO.deref h1 rb /\
    off' == BO.deref h2 rb /\
    U32.v off' == U32.v off + consumed1 /\
    b' == B.gsub b off (B.len b `U32.sub` off) /\
    b'_after == B.gsub b off' (B.len b `U32.sub` off') /\
    consumed <= Seq.length (B.as_seq h0 b) /\
    parse (parse_nlist (n) p0) (B.as_seq h0 b) == Some (l, consumed) /\
    consumed1 <= Seq.length (B.as_seq h0 b') /\
    parse p0 (B.as_seq h0 b') == Some (elem, consumed1) /\
    consumed_before <= Seq.length (B.as_seq h0 b') /\
    parse (parse_nlist (n - i) p0) (B.as_seq h0 b') == Some (l'_before, consumed_before) /\
    consumed_after <= Seq.length (B.as_seq h0 b'_after) /\
    parse (parse_nlist (n - (i + 1)) p0) (B.as_seq h0 b'_after) == Some (l'_after, consumed_after) /\
    BO.deref h2 rr == elem :: BO.deref h1 rr /\
    True
  ))
  (ensures (
    parse_nlist_impl_inv p0 n h0 b rb rr h2 (i + 1) false
  ))
= parse_nlist_eq (n - i) p0 (B.as_seq h0 b');
  assert (b'_after == B.gsub b' (U32.uint_to_t consumed1) (B.len b `U32.sub` off'));
  assert (consumed == U32.v off + consumed_before);
  let l1 = BO.deref h1 rr in
  assert (l == L.append (L.rev l1) l'_before);
  assert (consumed == U32.v off' + consumed_after);
  assert (l'_before == elem :: l'_after);
  list_assoc_append elem l1 l'_after;
  assert (l == L.append (L.rev (elem :: l1)) l'_after);
  assert (parse_nlist_impl_inv p0 n h0 b rb rr h2 (i + 1) false)

// (parse (parse_nlist (n + 1) p) b == match parse (parse_nlist n

inline_for_extraction
val parse_nlist_impl_body
  (#t: Type0)
  (p0: parser_spec t)
  (pimpl: parser_impl p0)
  (n: nat)
  (h0: HS.mem)
  (b: buffer8)
  (len: U32.t { len == B.len b } )
  (rb: B.pointer (x: U32.t { U32.v x <= B.length b } ))
  (rr: B.pointer (list t))
  (i: U32.t { 0 <= U32.v i /\ U32.v i < n } )
: HST.Stack bool
  (requires (fun h -> parse_nlist_impl_inv p0 n h0 b rb rr h (U32.v i) false))
  (ensures (fun h res h' ->
    parse_nlist_impl_inv p0 n h0 b rb rr h (U32.v i) false /\
    parse_nlist_impl_inv p0 n h0 b rb rr h' (U32.v i + 1) res
  ))

let parse_nlist_impl_body #t p0 pimpl n h0 b len rb rr i =
  let off = BO.op_Bang_Star rb in
  let b' = B.offset b off in
  assert (n - U32.v i > 0);
  let h = HST.get () in
  let h1 = h in
  match pimpl b' (len `U32.sub` off) with
  | None ->
    true
  | Some (elem, consumed) ->
    assert (let (Some (elem', consumed')) = parse p0 (B.as_seq h b') in elem == elem' /\ U32.v consumed == consumed');
    assert (U32.v consumed <= U32.v (len `U32.sub` off));
    let off' = off `U32.add` consumed in
    assert (len `U32.sub` off' == B.len b' `U32.sub` consumed);
    B.gsub_gsub b off (len `U32.sub` off) consumed (len `U32.sub` off');
    BO.op_Star_Equals rb off';
    let l1 = BO.op_Bang_Star rr in
    BO.op_Star_Equals rr (elem :: l1);
    let h = HST.get () in
//    assume (M.modifies (M.loc_union (M.loc_buffer rb) (M.loc_buffer rr)) h0 h);
    assert (parse_nlist_impl_inv_easy n h0 b rb rr h (U32.v i + 1) false);
    parse_nlist_eq (n - U32.v i) p0 (B.as_seq h0 b');
    let phi () : Lemma (parse_nlist_impl_inv p0 n h0 b rb rr h (U32.v i + 1) false) =
      let p = parse (parse_nlist n p0) (B.as_seq h0 b) in
      let i = U32.v i in
      let b'_after = B.gsub b off' (len `U32.sub` off') in
      assert (off' == BO.deref h rb);
      assert (b'_after == B.gsub b off' (B.len b `U32.sub` off'));
      let p'_before = parse (parse_nlist (n - i) p0) (B.as_seq h0 b') in
      let p'_after = parse (parse_nlist (n - (i + 1)) p0) (B.as_seq h0 b'_after) in
      assert (None? p == None? p'_before);
      assert (b'_after == B.gsub b' consumed (len `U32.sub` off'));
      assert (None? p'_before == None? p'_after);
      let consumed1 = U32.v consumed in
      match p, p'_before, p'_after with
      | Some (l, consumed), Some (l'_before, consumed'_before), Some (l'_after, consumed'_after) ->
        parse_nlist_impl_inv_false_intro p0 n h0 b rb rr h1 h i off off' b' b'_after l elem consumed1 consumed l'_before consumed'_before l'_after consumed'_after
      | _ -> ()
    in
    phi ();
    false

inline_for_extraction
let parse_nlist_impl
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser_spec t)
  (p32: parser_impl p)
: Tot (parser_impl (parse_nlist n p))
= fun b len ->
  HST.push_frame ();
  let rr : B.pointer (list t) = B.alloca [] 1ul in
  let rb : B.pointer (x: U32.t { U32.v x <= B.length b } ) = B.alloca 0ul 1ul in
  let h0 = HST.get () in
  let (_, stop) =
    CL.interruptible_for 0ul n'
      (parse_nlist_impl_inv p n h0 b rb rr)
      (parse_nlist_impl_body p p32 n h0 b len rb rr)
  in
  let l = BO.op_Bang_Star rr in
  let consumed = BO.op_Bang_Star rb in
  let res : option (nlist n t * U32.t) =
    if stop
    then None
    else Some (L.rev l, consumed)
  in
  HST.pop_frame ();
  res


assume val serialize_nlist_impl
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser_spec t)
  (#s: serializer_spec p)
  (s32: serializer_impl s)
: Tot (serializer_impl (serialize_nlist n s))
