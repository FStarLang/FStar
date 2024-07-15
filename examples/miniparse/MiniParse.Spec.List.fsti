(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module MiniParse.Spec.List
include MiniParse.Spec.Combinators // for seq_slice_append_l

module Seq = FStar.Seq
module L = FStar.List.Tot
module U32 = FStar.UInt32
module Classical = FStar.Classical

// inline_for_extraction
type nlist (n: nat) (t: Type) = (l: list t { L.length l == n } )

let nlist_nil (#t: Type) : Tot (nlist 0 t) = []

val nlist_nil_unique (t: Type) (l: nlist 0 t) : Lemma (l == nlist_nil)

let nlist_cons (#t: Type) (#n: nat) (a: t) (q: nlist n t) : Tot (nlist (n + 1) t) =
  a :: q

let nlist_destruct (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Tot (t & nlist n t) =
  let (a :: q) = x in
  a, q

val nlist_cons_unique (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Lemma
  (let (a, q) = nlist_destruct x in x == nlist_cons a q)

unfold let mul = Prims.op_Multiply

let synth_nlist (#t: Type) (n: nat) (xy: t & nlist n t) : Tot (nlist (n + 1) t) =
  let (x, y) = xy in
  nlist_cons x y

let synth_nlist_recip (#t: Type) (n: nat) (xy: nlist (n + 1) t) : Tot (t & nlist n t) =
  nlist_destruct xy

val synth_inverse_1 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist #t n) (synth_nlist_recip n))

val synth_inverse_2 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist_recip #t n) (synth_nlist n))

let rec parse_nlist'
  (n: nat)
  (#t: Type0)
  (p: parser_spec t)
: Tot (parser_spec (nlist n t))
= if n = 0
  then parse_ret nlist_nil
  else begin
    parse_synth
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
      (synth_nlist_recip (n - 1))
  end

val parse_nlist
  (n: nat)
  (#t: Type0)
  (p: parser_spec t)
: Tot (y: parser_spec (nlist n t) { y == parse_nlist' n p } )

let parse_nlist_eq
  (n: nat)
  (#t: Type0)
  (p: parser_spec t)
  (b: bytes)
: Tot (squash (
  parse (parse_nlist n p) b == (
    if n = 0
    then Some ([], 0)
    else match parse p b with
    | Some (elem, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      begin match parse (parse_nlist (n - 1) p) b' with
      | Some (q, consumed') -> Some (elem :: q, consumed + consumed')
      | _ -> None
      end
    | _ -> None
  )))
= if n = 0
  then ()
  else begin
    parse_synth_eq
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
      (synth_nlist_recip (n - 1))
      b;
    nondep_then_eq p (parse_nlist' (n - 1) p) b
  end

let rec serialize_nlist'
  (n: nat)
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
: Tot (serializer_spec (parse_nlist n p))
= if n = 0
  then begin
    Classical.forall_intro (nlist_nil_unique t);
    Serializer (fun _ -> Seq.empty)
  end
  else begin
    synth_inverse_1 t (n - 1);
    synth_inverse_2 t (n - 1);
    serialize_synth (serialize_nondep_then s (serialize_nlist' (n - 1) s)) (synth_nlist (n - 1)) (synth_nlist_recip (n - 1)) ()
  end

val serialize_nlist
  (n: nat)
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
: Tot (y: serializer_spec (parse_nlist n p) { y == serialize_nlist' n s })

val serialize_nlist_nil
  (#t: Type0)
  (p: parser_spec t)
  (s: serializer_spec p)
: Lemma
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.empty))

#set-options "--z3rlimit 16"

val serialize_list_cons
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

val serialize_list_singleton
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (a: t)
: Lemma
  (ensures (serialize (serialize_nlist 1 s) [a] == serialize s a))

val list_length_append (l1:list 'a) (l2:list 'a) :
  Lemma (requires True)
        (ensures (L.length (l1 `L.append` l2) == L.length l1 + L.length l2)) [SMTPat (L.length (l1 `L.append` l2))]

val serialize_list_append
  (#t: Type0)
  (n1 n2: nat)
  (#p: parser_spec t)
  (s: serializer_spec p)
  (l1: nlist n1 t)
  (l2: nlist n2 t)
: Lemma
  (ensures (serialize (serialize_nlist (n1 + n2) s) (L.append l1 l2 <: nlist (n1 + n2) t) == Seq.append (serialize (serialize_nlist n1 s) l1) (serialize (serialize_nlist n2 s) l2)))
