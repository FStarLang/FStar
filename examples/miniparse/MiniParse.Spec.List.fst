module MiniParse.Spec.List
include MiniParse.Spec.Combinators // for seq_slice_append_l

module Seq = FStar.Seq
module L = FStar.List.Tot
module U32 = FStar.UInt32
module Classical = FStar.Classical

inline_for_extraction
let nlist (n: nat) (t: Type) : Tot Type0 =
  (l: list t { L.length l == n } )

unfold let mul = Prims.op_Multiply

let parse_nlist_kind (n: nat) (k: parser_kind) : Tot parser_kind =
  {
    parser_kind_low = n `mul` k.parser_kind_low;
    parser_kind_high = if n = 0 then Some 0 else if Some? k.parser_kind_high then Some (n `mul` Some?.v k.parser_kind_high) else None;
    parser_kind_subkind = if n = 0 then Some ParserStrong else k.parser_kind_subkind;
  }

let rec parse_nlist_kind' (n: nat) (k: parser_kind) : GTot (k' : parser_kind { k' == parse_nlist_kind n k } ) =
  if n = 0
  then parse_ret_kind
  else k `and_then_kind` parse_nlist_kind' (n - 1) k

let synth_nlist (#t: Type) (n: nat) (xy: t * nlist n t) : Tot (nlist (n + 1) t) =
  let (x, y) = xy in
  x :: y

let rec parse_nlist
  (n: nat)
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot (parser (parse_nlist_kind n k) (nlist n t))
= [@inline_let]
  let _ : squash (parse_nlist_kind' n k == parse_nlist_kind n k) = () in
  if n = 0
  then parse_ret []
  else (p `nondep_then` parse_nlist (n - 1) p) `parse_synth` (synth_nlist (n - 1))

unfold
let serialize_list_precond
  (k: parser_kind)
: GTot bool
= k.parser_kind_subkind = Some ParserStrong &&
  k.parser_kind_low > 0

let synth_nlist_recip (#t: Type) (n: nat) (xy: nlist (n + 1) t) : Tot (t * nlist n t) =
  let (x :: y) = xy in
  (x , y)

let rec serialize_nlist
  (n: nat)
  (#t: Type0)
  (#k: parser_kind { serialize_list_precond k } )
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_nlist n p))
= [@inline_let]
  let _ : squash (parse_nlist_kind' n k == parse_nlist_kind n k) = () in
  if n = 0
  then fun _ -> Seq.createEmpty
  else serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then _ s () _ (serialize_nlist (n - 1) s)) (synth_nlist_recip (n - 1)) ()

let serialize_nlist_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.createEmpty))
= ()

let serialize_list_cons
  (#k: parser_kind)
  (#t: Type0)
  (n: nat)
  (#p: parser k t)
  (s: serializer p)
  (a: t)
  (q: nlist n t)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (
    serialize (serialize_nlist (n + 1) s) (a :: q) == Seq.append (serialize s a) (serialize (serialize_nlist n s) q)
  ))
= ()

let serialize_list_singleton
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (a: t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize (serialize_nlist 1 s) [a] == serialize s a))
= Seq.append_empty_r (serialize s a)

let list_length_append (l1:list 'a) (l2:list 'a) :
  Lemma (requires True)
        (ensures (L.length (l1 `L.append` l2) == L.length l1 + L.length l2)) [SMTPat (L.length (l1 `L.append` l2))]
= L.append_length l1 l2

let rec serialize_list_append
  (#k: parser_kind)
  (#t: Type0)
  (n1 n2: nat)
  (#p: parser k t)
  (s: serializer p)
  (l1: nlist n1 t)
  (l2: nlist n2 t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize_list_precond k /\ serialize (serialize_nlist (n1 + n2) s) (L.append l1 l2 <: nlist (n1 + n2) t) == Seq.append (serialize (serialize_nlist n1 s) l1) (serialize (serialize_nlist n2 s) l2)))
= match l1 with
  | a :: q ->
    serialize_list_append (n1 - 1) n2 s q l2;
    serialize_list_cons (n1 - 1 + n2) s a (L.append q l2);
    Seq.append_assoc (serialize s a) (serialize (serialize_nlist (n1 - 1) s) q) (serialize (serialize_nlist n2 s) l2)
  | [] ->
    serialize_nlist_nil p s;
    Seq.append_empty_l (serialize (serialize_nlist n2 s) l2)
