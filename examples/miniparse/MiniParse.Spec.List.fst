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

let nlist_nil_unique (t: Type) (l: nlist 0 t) : Lemma (l == nlist_nil) = ()

let nlist_cons_unique (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Lemma
  (let (a, q) = nlist_destruct x in x == nlist_cons a q)
= ()

let synth_inverse_1 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist #t n) (synth_nlist_recip n))
= ()

// abstract
let synth_inverse_2 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist_recip #t n) (synth_nlist n))
= ()

let parse_nlist
  (n: nat)
  (#t: Type0)
  (p: parser_spec t)
: Tot (y: parser_spec (nlist n t) { y == parse_nlist' n p } )
= parse_nlist' n p

let serialize_nlist
  (n: nat)
  (#t: Type0)
  (#p: parser_spec t)
  (s: serializer_spec p)
: Tot (y: serializer_spec (parse_nlist n p) { y == serialize_nlist' n s })
= serialize_nlist' n s

let serialize_nlist_nil
  (#t: Type0)
  (p: parser_spec t)
  (s: serializer_spec p)
: Lemma
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.empty))
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
