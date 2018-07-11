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

let synth_nlist (#t: Type) (n: nat) (xy: t * nlist n t) : Tot (nlist (n + 1) t) =
  let (x, y) = xy in
  x :: y

let synth_nlist_recip (#t: Type) (n: nat) (xy: nlist (n + 1) t) : Tot (t * nlist n t) =
  let (x :: y) = xy in
  (x , y)

let rec parse_nlist
  (n: nat)
  (#t: Type0)
  (p: parser_spec t)
: Tot (parser_spec (nlist n t))
= if n = 0
  then parse_ret []
  else
    parse_synth
      (p `nondep_then` parse_nlist (n - 1) p)
      (synth_nlist (n - 1))
      (synth_nlist_recip (n - 1))

let rec serialize_nlist
  (n: nat)
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
: Tot (serializer_spec (parse_nlist n p))
= if n = 0
  then Serializer (fun _ -> Seq.empty)
  else serialize_synth (serialize_nondep_then s (serialize_nlist (n - 1) s)) (synth_nlist (n - 1)) (synth_nlist_recip (n - 1)) ()

let serialize_nlist_nil
  (#t: Type0)
  (p: parser_spec t)
  (s: serializer_spec p)
: Lemma
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.createEmpty))
= ()

#set-options "--z3rlimit 16"

let serialize_list_cons
  (#t: Type0)
  (n: nat)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (a: t)
  (q: nlist n t)
: Lemma
  (ensures (
    serialize (serialize_nlist (n + 1) s) (a :: q) == Seq.append (serialize s a) (serialize (serialize_nlist n s) q)
  ))
= ()

let serialize_list_singleton
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (a: t)
: Lemma
  (ensures (serialize (serialize_nlist 1 s) [a] == serialize s a))
= Seq.append_empty_r (serialize s a)

let list_length_append (l1:list 'a) (l2:list 'a) :
  Lemma (requires True)
        (ensures (L.length (l1 `L.append` l2) == L.length l1 + L.length l2)) [SMTPat (L.length (l1 `L.append` l2))]
= L.append_length l1 l2

let rec serialize_list_append
  (#t: Type0)
  (n1 n2: nat)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (l1: nlist n1 t)
  (l2: nlist n2 t)
: Lemma
  (ensures (serialize (serialize_nlist (n1 + n2) s) (L.append l1 l2 <: nlist (n1 + n2) t) == Seq.append (serialize (serialize_nlist n1 s) l1) (serialize (serialize_nlist n2 s) l2)))
= match l1 with
  | a :: q ->
    serialize_list_append (n1 - 1) n2 s q l2;
    serialize_list_cons (n1 - 1) s a q;
    serialize_list_cons (n1 - 1 + n2) s a (L.append q l2);
    Seq.append_assoc (serialize s a) (serialize (serialize_nlist (n1 - 1) s) q) (serialize (serialize_nlist n2 s) l2)
  | [] ->
    serialize_nlist_nil p s;
    Seq.append_empty_l (serialize (serialize_nlist n2 s) l2)
