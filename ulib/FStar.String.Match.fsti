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

module FStar.String.Match

open FStar.String
open FStar.String.Base

///  Return the first difference position as an option for the whole string.
val first_diff (s1 s2: string) : 
   Tot (o : (option (pos: nat{pos <= (min (strlen s1) (strlen s2))})) {
             (None? o ==> strlen s1 = strlen s2 /\ streq_upto s1 s2 (strlen s1)) /\
             (Some? o ==> 
               streq_upto_min s1 s2 (Some?.v o) /\
              (((Some?.v o) = strlen s1  \/ (Some?.v o) = strlen s2) /\ strlen s1 <> strlen s2)
              \/
              (((Some?.v o) < strlen s1 /\ (Some?.v o) < strlen s2) /\
                (index s1 (Some?.v o) <> (index s2 (Some?.v o)))))
        })


///  Return the line and character upto pos counting each starting at zero.
val lines (s: string) (upto: nat{upto <= strlen s}) :  Tot (nat & nat) 

val none_first_diff_impl_index_extensionality (s1 s2: string) :
  Lemma (None? (first_diff s1 s2) ==>
          length s1 = length s2 /\
          (forall (i: nat) . i < length s1 ==> index s1 i = index s2 i))

val none_first_diff_impl_deq (s1 s2: string) :
  Lemma (None? (first_diff s1 s2) ==> s1 = s2)

val deq_impl_none_first_diff (s1 s2: string) :
  Lemma (s1 = s2 ==> None? (first_diff s1 s2))

val deq_iff_none_first_diff (s1 s2: string) :
  Lemma (s1 = s2 <==> None? (first_diff s1 s2))

val first_diff_strlen_neq (s1 s2 : string) :
 Lemma (strlen s1 <> strlen s2 ==> Some? (first_diff s1 s2 ))

val first_diff_neq_some (s1 s2 : string) :
 Lemma (s1 <> s2 ==> Some? (first_diff s1 s2))
