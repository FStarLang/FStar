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

open FStar.String
open FStar.String.Base

///  Length properties

val strlen_is_list_length (s: string) :
 Lemma (strlen s = List.Tot.length (list_of_string s))

val list_length_is_strlen (lc: list char) :
 Lemma (strlen (string_of_list lc) = List.Tot.length lc)

val deq_lengths (s1 s2: string) :
 Lemma (s1 = s2 ==> strlen s1 = strlen s2)

val strlen_string_of_char (c: char) :
 Lemma ((strlen (string_of_char c)) = 1)

///  Generalized list_of_string and string_of_list 

val indexes_deq_list_of_string (s:string)  :
  Lemma (forall (i : nat{i < length s}). List.Tot.index (list_of_string s) i == index s i)

val indexes_deq_string_of_list (lc: list char)  :
  Lemma (list_of_string_of_list lc;
         forall (i : nat{i < List.Tot.length lc}). 
            index (string_of_list lc) i == List.Tot.index lc i)

///  Deq at all indexes gives you string equality.

val index_extensionality (s1 s2: string) :
 Lemma
  (requires
    strlen s1 = strlen s2 /\
     (forall (i: nat) . i < strlen s1 ==> index s1 i = index s2 i))
  (ensures (s1 == s2))

///  Streq_upto properties

val streq_upto_strlen_impl_deq s1 s2 :
  Lemma (requires strlen s1 = strlen s2)
        (ensures streq_upto s1 s2 (strlen s1) ==> s1 = s2)

val streq_impl_streq_upto_strlen s1 s2 :
  Lemma (s1 = s2 ==> streq_upto s1 s2 (strlen s1))

val streq_iff_streq_upto_strlen s1 s2 :
  Lemma (requires strlen s1 = strlen s2)
        (ensures s1 = s2 <==> streq_upto s1 s2 (strlen s1))

val streq_upto_zero s1 (s2: string{strlen s1 = strlen s2}) :
  Lemma (streq_upto s1 s2 0)

///  Empty string properties.

val strlen_empty () :
  Lemma (strlen "" = 0)
