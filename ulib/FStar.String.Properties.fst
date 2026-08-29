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
   Author: Brian Milnes <briangmilnes@gmail.com>

*)

module FStar.String.Properties

///  Length properties

let strlen_is_list_length (s: string) :
 Lemma (strlen s = List.Tot.length (list_of_string s))
= ()

let list_length_is_strlen (lc: list char) :
 Lemma (strlen (string_of_list lc) = List.Tot.length lc)
= list_of_string_of_list lc

let deq_lengths (s1 s2: string) :
 Lemma (s1 = s2 ==> strlen s1 = strlen s2)
= ()

let strlen_string_of_char (c: char) :
 Lemma ((strlen (string_of_char c)) = 1)
= ()

///  Index properties

let indexes_deq_list_of_string (s:string)  :
  Lemma (forall (i : nat{i < length s}). List.Tot.index (list_of_string s) i == index s i)
= introduce forall (i : nat{i < length s}). List.Tot.index (list_of_string s) i == index s i
  with index_list_of_string s i

let indexes_deq_string_of_list (lc: list char)  :
  Lemma (list_of_string_of_list lc;
         forall (i : nat{i < List.Tot.length lc}). 
            index (string_of_list lc) i == List.Tot.index lc i)
= list_of_string_of_list lc;
  introduce forall (i : nat{i < List.Tot.length lc}). 
             index (string_of_list lc) i == List.Tot.index lc i
  with index_string_of_list lc i


let index_extensionality (s1 s2: string)
: Lemma
  (requires
    (strlen s1 = strlen s2 /\
    (forall (i: nat) . i < strlen s1 ==> index s1 i = index s2 i)))
  (ensures (s1 = s2))
= let l1 = (list_of_string s1) in 
  let l2 = (list_of_string s2) in
  indexes_deq_list_of_string s1;
  indexes_deq_list_of_string s2;
  List.Tot.index_extensionality l1 l2;
  string_of_list_of_string s1;
  string_of_list_of_string s2

///  Streq_upto properties

let streq_upto_strlen_impl_deq s1 s2 :
  Lemma (requires strlen s1 = strlen s2)
        (ensures streq_upto s1 s2 (strlen s1) ==> s1 = s2)
= introduce streq_upto s1 s2 (strlen s1) ==> s1 = s2 
  with pf_streq_upto . begin
   pf_streq_upto;
   index_extensionality s1 s2
  end

let streq_impl_streq_upto_strlen s1 s2 :
  Lemma (s1 = s2 ==> streq_upto s1 s2 (strlen s1))
= ()

let streq_iff_streq_upto_strlen s1 s2 :
  Lemma (requires strlen s1 = strlen s2)
        (ensures s1 = s2 <==> streq_upto s1 s2 (strlen s1))
= streq_impl_streq_upto_strlen s1 s2;
  streq_upto_strlen_impl_deq   s1 s2

let streq_upto_zero s1 (s2: string{strlen s1 = strlen s2}) :
  Lemma (streq_upto s1 s2 0)
= ()

///  Empty string properties.

let strlen_empty () :
  Lemma (strlen "" = 0)
= assert_norm(strlen "" = 0) 
