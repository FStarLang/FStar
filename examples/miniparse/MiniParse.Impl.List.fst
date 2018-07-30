module MiniParse.Impl.List
include MiniParse.Spec.List
include MiniParse.Impl.Base
include MiniParse.Impl.Combinators // for seq_append_slice

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
= parse_nlist_impl_inv_easy n h0 b rb rr h i /\ (
  let off = B.deref h rb in
  let b' = B.gsub b off (B.len b `U32.sub` off) in
  let p = parse (parse_nlist n p0) (B.as_seq h0 b) in
  let p' = parse (parse_nlist (n - i) p0) (B.as_seq h0 b') in
  if stop
  then None? p
  else match p, p' with
  | Some (l, consumed), Some (l', consumed') ->
    consumed == U32.v off + consumed' /\
    l == L.append (L.rev (B.deref h rr)) l'
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
    parse_nlist_impl_inv_easy n h0 b rb rr h2 (i + 1) /\
    off == B.deref h1 rb /\
    off' == B.deref h2 rb /\
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
    B.deref h2 rr == elem :: B.deref h1 rr /\
    True
  ))
  (ensures (
    parse_nlist_impl_inv p0 n h0 b rb rr h2 (i + 1) false
  ))
= parse_nlist_eq (n - i) p0 (B.as_seq h0 b');
  assert (b'_after == B.gsub b' (U32.uint_to_t consumed1) (B.len b `U32.sub` off'));
  assert (consumed == U32.v off + consumed_before);
  let l1 = B.deref h1 rr in
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
    assert (parse_nlist_impl_inv_easy n h0 b rb rr h (U32.v i + 1));
    parse_nlist_eq (n - U32.v i) p0 (B.as_seq h0 b');
    let phi () : Lemma (parse_nlist_impl_inv p0 n h0 b rb rr h (U32.v i + 1) false) =
      let p = parse (parse_nlist n p0) (B.as_seq h0 b) in
      let i = U32.v i in
      let b'_after = B.gsub b off' (len `U32.sub` off') in
      assert (off' == B.deref h rb);
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

#reset-options

let list_rev_inv
  (#t: Type)
  (l: list t)
  (b: bool)
  (x: list t * list t)
: GTot Type0
= let (rem, acc) = x in
  L.rev l == L.rev_acc rem acc /\
  (b == false ==> rem == [])

let list_rev
  (#t: Type)
  (l: list t)
: Tot (l' : list t { l' == L.rev l } )
= match l with
  | [] -> []
  | _ ->
    let (_, l') =
      CL.total_while
        (fun (rem, _) -> L.length rem)
        (list_rev_inv l)
        (fun (rem, acc) ->
          match rem with
          | [] -> (false, (rem, acc))
          | a :: q -> (true, (q, a :: acc))
        )
        (l, [])
    in
    l'

#set-options "--z3rlimit 64"

inline_for_extraction
let parse_nlist_impl
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser_spec t)
  (p32: parser_impl p)
: Tot (parser_impl (parse_nlist n p))
= fun b len ->
  let h0 = HST.get () in
  HST.push_frame ();
  let rr : B.pointer (list t) = B.alloca [] 1ul in
  let rb : B.pointer (x: U32.t { U32.v x <= B.length b } ) = B.alloca 0ul 1ul in
  let h1 = HST.get () in
  assert (parse_nlist_impl_inv p n h1 b rb rr h1 0 false);
  let (_, stop) =
    CL.interruptible_for 0ul n'
      (parse_nlist_impl_inv p n h1 b rb rr)
      (parse_nlist_impl_body p p32 n h1 b len rb rr)
  in
  let l = BO.op_Bang_Star rr in
  let l' = list_rev l in
  let consumed = BO.op_Bang_Star rb in
  let res : option (nlist n t * U32.t) =
    if stop
    then None
    else Some (l', consumed)
  in
  HST.pop_frame ();
  let h = HST.get () in
  assert (M.modifies M.loc_none h0 h);
  let phi () : Lemma (
    match parse (parse_nlist n p) (B.as_seq h0 b), res with
    | None, None -> True
    | Some (y, consumed), Some (y', consumed') -> y == y' /\ U32.v consumed' == consumed
    | _ -> False    
  )
  = if stop
    then ()
    else begin
      assert (n - n == 0);
      parse_nlist_eq 0 p (B.as_seq h0 (B.gsub b 0ul (B.len b `U32.sub` consumed)));
      L.append_l_nil l';
      ()
    end
  in
  phi ();
  res

let serialize_nlist_impl_inv_easy
  (#t: Type0)
  (n: nat)
  (h0: HS.mem)
  (b: buffer8)
  (rb: B.pointer (x: U32.t { U32.v x <= B.length b } ))
  (rr: B.pointer (list t))
  (h: HS.mem)
  (i: nat)
: Tot Type0
= M.loc_disjoint (M.loc_buffer rb) (M.loc_buffer rr) /\
  M.loc_disjoint (M.loc_buffer b) (M.loc_union (M.loc_buffer rb) (M.loc_buffer rr)) /\
  i <= n /\
  B.live h0 b /\ B.live h b /\ B.live h rb /\ B.live h rr

let serialize_nlist_impl_inv
  (n: nat)
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (b: buffer8)
  (h0: HS.mem)
  (l: nlist n t)
  (rr: B.pointer (list t))
  (rb: B.pointer (u: U32.t { U32.v u <= B.length b } ))
  (h: HS.mem)
  (i: nat)
  (stop: bool)
: Tot Type0
= serialize_nlist_impl_inv_easy n h0 b rb rr h i /\ (
  let off = B.deref h rb in
  let bl = B.gsub b 0ul off in
  let ser = serialize (serialize_nlist n s) l in
  let ll = B.deref h rr in
  if stop
  then (
    M.modifies (M.loc_union (M.loc_buffer b) (M.loc_union (M.loc_buffer rb) (M.loc_buffer rr))) h0 h /\
    Seq.length ser > B.length b
  )
  else (    
    M.modifies (M.loc_union (M.loc_buffer bl) (M.loc_union (M.loc_buffer rb) (M.loc_buffer rr))) h0 h /\
    L.length ll == n - i /\
    ser == Seq.append (B.as_seq h bl) (serialize (serialize_nlist (n - i) s) ll)
  ))

inline_for_extraction
let serialize_nlist_impl_body
  (n: nat)
  (#t: Type0)
  (#p: parser_spec t)
  (#s: serializer_spec p)
  (s32: serializer_impl s)
  (b: buffer8)
  (len: U32.t { len == B.len b } )
  (h0: HS.mem)
  (l: nlist n t)
  (rr: B.pointer (list t))
  (rb: B.pointer (u: U32.t { U32.v u <= B.length b } ))
  (i: U32.t { 0 <= U32.v i /\ U32.v i < n } )
: HST.Stack bool
  (requires (fun h -> serialize_nlist_impl_inv n s b h0 l rr rb h (U32.v i) false))
  (ensures (fun h stop h' ->
    serialize_nlist_impl_inv n s b h0 l rr rb h (U32.v i) false /\
    serialize_nlist_impl_inv n s b h0 l rr rb h' (U32.v i + 1) stop
  ))
= let off = BO.op_Bang_Star rb in
  let b' = B.offset b off in
  let aq = BO.op_Bang_Star rr in
  let (a :: q) = aq in
  serialize_list_cons (n - (U32.v i + 1)) s a q;
  match s32 b' (len `U32.sub` off) a with
  | None ->
    true
  | Some consumed ->
    let off' = off `U32.add` consumed in
    BO.op_Star_Equals rb off';
    BO.op_Star_Equals rr q;
    let h = HST.get () in
    let phi () : Lemma
      (serialize_nlist_impl_inv n s b h0 l rr rb h (U32.v i + 1) false)
    =
      assert_norm (U32.v 0ul == 0);
      assert (U32.v off <= B.length b);
      let bl_before = B.gsub b 0ul off in
      let bl_after = B.gsub b 0ul off' in
      let be = B.gsub b off consumed in
      assert (B.as_seq h be == serialize s a);
      seq_append_slice (B.as_seq h b) (U32.v off) (U32.v consumed);
      assert (B.as_seq h bl_after == (B.as_seq h bl_before `Seq.append` B.as_seq h be));
      Seq.append_assoc (B.as_seq h bl_before) (serialize s a) (serialize (serialize_nlist (n - (U32.v i + 1)) s) q);
      assert (bl_before == B.gsub bl_after 0ul off);
      assert (be == B.gsub bl_after off consumed);
      assert (serialize_nlist_impl_inv n s b h0 l rr rb h (U32.v i + 1) false)
    in
    phi ();
    false

inline_for_extraction
let serialize_nlist_impl
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser_spec t)
  (#s: serializer_spec p)
  (s32: serializer_impl s)
: Tot (serializer_impl (serialize_nlist n s))
= fun b len l ->
  let h0 = HST.get () in
  HST.push_frame ();
  let rr : B.pointer (list t) = B.alloca l 1ul in
  let rb : B.pointer (x: U32.t { U32.v x <= B.length b } ) = B.alloca 0ul 1ul in
  let h1 = HST.get () in
  assert (B.as_seq h1 (B.gsub b 0ul 0ul) `Seq.equal` Seq.empty);
  Seq.append_empty_l (serialize (serialize_nlist n s) l);
  assert (serialize_nlist_impl_inv n s b h1 l rr rb h1 0 false);
  let (_, stop) =
    CL.interruptible_for 0ul n'
      (serialize_nlist_impl_inv n s b h1 l rr rb)
      (serialize_nlist_impl_body n s32 b len h1 l rr rb)
  in
  let consumed = BO.op_Bang_Star rb in
  let res : option U32.t =
    if stop
    then None
    else Some consumed
  in
  HST.pop_frame ();
  let h = HST.get () in
  let phi () : Lemma (
    let len = Seq.length (serialize (serialize_nlist n s) l) in
    match res with
    | None ->
      M.modifies (M.loc_buffer b) h h /\ len > B.length b
    | Some len' ->
      U32.v len' == len /\
      len <= B.length b /\ (
      let b' = B.gsub b 0ul len' in
      M.modifies (M.loc_buffer b') h0 h /\
      B.as_seq h b' == serialize (serialize_nlist n s) l
  )) =
    if stop
    then ()
    else begin
      let b' = B.gsub b 0ul consumed in
      assert (M.modifies (M.loc_buffer b') h0 h);
      assert (n - n == 0);
      serialize_nlist_nil p s;
      assert (Seq.createEmpty #byte `Seq.equal` Seq.empty);
      Seq.append_empty_r (B.as_seq h b');
      ()
    end
  in
  phi ();
  res
