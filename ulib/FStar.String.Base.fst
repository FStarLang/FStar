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
module FStar.String.Base

let rec streq_upto'' (s1: string) (s2: string{strlen s1 = strlen s2})
                     (to: nat{to <= strlen s1}) (from: nat{from <= strlen s1 /\ streq_upto s1 s2 from /\ from <= to}):
  Tot (b:bool{b <==> streq_upto s1 s2 to})
  (decreases strlen s1 - from)
=     
 if from = to 
 then true
 else if from = strlen s1 
 then true
 else if index s1 from <> index s2 from
 then false 
 else streq_upto'' s1 s2 to (from+1)

let streq_upto' s1 (s2: string{strlen s1 = strlen s2}) (to: nat{to <= strlen s1}):
  Tot (b:bool{b <==> streq_upto s1 s2 to})
= streq_upto'' s1 s2 to 0
