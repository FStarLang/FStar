(*
   Copyright 2024 Microsoft Research

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

module FStar.String.Properties

open FStar.String

///  Length properties

let strlen_is_list_length (s: string) :
 Lemma (strlen s = List.Tot.length (list_of_string s))
= ()

let list_length_is_strlen (lc: list char) :
 Lemma (strlen (string_of_list lc) = List.Tot.length lc)
= list_of_string_of_list lc

let streq_eq_lengths (s1 s2: string) :
 Lemma (streq s1 s2 ==> strlen s1 = strlen s2)
= ()

let streq'_eq_lengths (s1 s2: string) :
 Lemma (streq' s1 s2 ==> strlen s1 = strlen s2)
= ()

let strlen_string_of_char (c: char) :
 Lemma ((strlen (string_of_char c)) = 1)
= ()

///  Index properties

let indexes_eq_list_of_string (s:string)  :
  Lemma (forall (i : nat{i < length s}). List.Tot.index (list_of_string s) i == index s i)
= introduce forall (i : nat{i < length s}). List.Tot.index (list_of_string s) i == index s i
  with index_list_of_string s i

// Could be done with indexes_eq_list_of_string, but FStar.String does it with
// list_of_string_of_list lc.
let indexes_eq_string_of_list (lc: list char)  :
  Lemma (list_of_string_of_list lc;
         forall (i : nat{i < List.Tot.length lc}). 
            index (string_of_list lc) i == List.Tot.index lc i)
= list_of_string_of_list lc;
  introduce forall (i : nat{i < List.Tot.length lc}). 
             index (string_of_list lc) i == List.Tot.index lc i
  with index_string_of_list lc i

///  Relation Properties for streq

let streq_refl (s: string) : 
 Lemma (ensures  streq s s) 
= ()

let streq_sym (s1 s2: string) : 
  Lemma (requires streq s1 s2) (ensures streq s2 s1)
= ()

let streq_trans (s1 s2 s3: string) :
 Lemma (requires streq s1 s2 /\ streq s2 s3)
       (ensures  streq s1 s2)
= ()

///  Streq_upto properties

let streq_upto_strlen_impl_streq s1 s2 :
  Lemma (requires streq_upto s1 s2 (strlen s1) /\ strlen s1 = strlen s2)
        (ensures  streq s1 s2)
= ()

let streq_impl_streq_upto_strlen s1 s2 :
  Lemma (requires  streq s1 s2)
        (ensures streq_upto s1 s2 (strlen s1))
= ()

let streq_iff_streq_upto_strlen s1 s2 :
  Lemma (requires strlen s1 = strlen s2)
        (ensures streq s1 s2 <==> streq_upto s1 s2 (strlen s1))
= 
  assert(streq s1 s2 ==> streq_upto s1 s2 (strlen s1));
  assert(streq_upto s1 s2 (strlen s1) ==> streq s1 s2)

let streq_upto_zero s1 (s2: string{strlen s1 = strlen s2}) :
  Lemma (streq_upto s1 s2 0)
= ()

///  Streq equivalance to streq'.

let streq_impl_streq' s1 (s2: string{strlen s1 = strlen s2}) :
 Lemma (streq s1 s2 ==> streq' s1 s2)
= ()

let streq'_impl_streq s1 (s2: string{strlen s1 = strlen s2}) :
 Lemma (streq' s1 s2 ==> streq s1 s2)
= ()

let streq'_iff_streq s1 (s2: string{strlen s1 = strlen s2}) :
 Lemma (streq' s1 s2 <==> streq s1 s2)
= ()

///  streq' equivalance to decideable equality.

let streq'_impl_eq (s1 s2: string) :
  Lemma (streq' s1 s2 ==> s1 = s2)
= introduce streq' s1 s2 ==> s1 = s2
  with pf_streq_s1_s2 .
  begin
   assert(strlen s1 = strlen s2);
   assert(forall (i: nat{i < strlen s1}). index s1 i = index s2 i);
   let l1 = (list_of_string s1) in
   let l2 = (list_of_string s2) in
     strlen_is_list_length s1;
     strlen_is_list_length s2;
     assert(List.length l1 == List.length l2);
     indexes_eq_list_of_string s1;
     indexes_eq_list_of_string s2;
     assert(forall (i: nat) . i < List.length l1 ==> List.Tot.index l1 i == List.Tot.index l2 i);
     List.Tot.index_extensionality l1 l2;
     assert(l1 == l2);
     string_of_list_of_string s1;
     assert(string_of_list l1 == s1);
     string_of_list_of_string s2;
     assert(string_of_list l2 == s2)
  end

let eq_impl_streq' (s1 s2: string) :
  Lemma (s1 = s2 ==> streq' s1 s2)
= ()

let streq'_iff_eq (s1 s2: string) :
  Lemma (streq' s1 s2 <==> s1 = s2)
= streq'_impl_eq s1 s2;
  eq_impl_streq' s1 s2


///  streq' equivalance to propositional equality.

let streq'_impl_propeq (s1 s2: string) :
  Lemma (streq' s1 s2 ==> s1 == s2)
= streq'_impl_eq s1 s2

let propeq_impl_streq' (s1 s2: string) :
  Lemma (s1 == s2 ==> streq' s1 s2)
= ()

let streq'_iff_propeq (s1 s2: string) :
  Lemma (streq' s1 s2 <==> s1 == s2)
= streq'_impl_propeq s1 s2;
  propeq_impl_streq' s1 s2

///  streq equivalence to propositional equality.

let streq_impl_propeq (s1 s2: string) :
 Lemma (streq s1 s2 ==> s1 == s2)
= streq'_impl_eq s1 s2

let propeq_impl_streq (s1 s2: string) :
 Lemma (s1 == s2 ==> streq s1 s2)
= ()

let streq_iff_propeq (s1 s2: string) :
 Lemma (streq s1 s2 <==> s1 == s2)
= streq_impl_propeq s1 s2;
  propeq_impl_streq s1 s2

///  streq equivalence to propositional equality.

let streq_impl_deq (s1 s2: string) :
 Lemma (streq s1 s2 ==> s1 = s2)
= streq_impl_propeq s1 s2

let deq_impl_streq (s1 s2: string) :
 Lemma (s1 = s2 ==> streq s1 s2)
= ()

let streq_iff_deq (s1 s2: string) :
 Lemma (streq s1 s2 <==> s1 = s2)
= streq_impl_deq s1 s2;
  deq_impl_streq s1 s2

///  Empty string properties.

let strlen_empty () :
  Lemma (strlen "" = 0)
= assert(strlen "" = 0) by FStar.Tactics.V2.compute()

///  Difference Properties

let first_diff'_none_strlen_same (s1 s2: string) :
  Lemma (None? (first_diff' s1 s2 0) ==> strlen s1 = strlen s2)
= ()

let none_first_diff_impl_streq (s1 s2: string) :
  Lemma (None? (first_diff s1 s2) ==> streq s1 s2)
= ()

let streq_impl_none_first_diff (s1 s2: string) :
  Lemma (streq s1 s2 ==> None? (first_diff s1 s2))
= ()

let streq_iff_none_first_diff (s1 s2: string) :
  Lemma (streq s1 s2 <==> None? (first_diff s1 s2))
= none_first_diff_impl_streq s1 s2;
  streq_impl_none_first_diff s1 s2

let first_diff_strlen_neq (s1 s2 : string) :
 Lemma (strlen s1 <> strlen s2 ==> Some? (first_diff s1 s2 ))
= ()

let first_diff_neq_some (s1 s2 : string) :
 Lemma (s1 <> s2 ==> Some? (first_diff s1 s2))
= if strlen s1 <> strlen s2 
  then first_diff_strlen_neq s1 s2
  else 
    match first_diff s1 s2 with
    | Some d -> ()
    | None   -> begin 
       none_first_diff_impl_streq s1 s2;
       assert(streq s1 s2);
       streq_impl_deq s1 s2
     end 
