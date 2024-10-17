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

module FStar.String.Base

open FStar.String

let rec streq_upto' s1 (s2: string{strlen s1 = strlen s2})  (pos: nat{streq_upto s1 s2 pos}) :
  Tot (b:bool{b <==> streq s1 s2})
  (decreases strlen s1 - pos)
=     
 if pos = strlen s1 
 then true
 else if index s1 pos = index s2 pos
 then streq_upto' s1 s2 (pos+1)
 else false

let streq' (s1 s2: string) : Tot (b:bool{b <==> streq s1 s2})
=
  if strlen s1 <> strlen s2
  then false
  else streq_upto' s1 s2 0 

let rec first_diff' s1 s2
   (pos: nat{pos <= strlen s1 /\ pos <= strlen s2 /\ streq_upto s1 s2 pos}) : 
   Tot (o : (option (pos: nat{pos <= (min (strlen s1) (strlen s2))})) {
             (None? o ==> strlen s1 = strlen s2 /\ streq_upto s1 s2 (strlen s1)) /\
             (Some? o ==> 
               streq_upto_min s1 s2 ((Some?.v o) - 1) /\
              (((Some?.v o) = strlen s1  \/ (Some?.v o) = strlen s2) /\ strlen s1 <> strlen s2)
              \/
              (((Some?.v o) < strlen s1 /\ (Some?.v o) < strlen s2) /\
                (index s1 (Some?.v o) <> (index s2 (Some?.v o)))))
        })
       (decreases (strlen s1 - pos))
=
 if pos = strlen s1 && pos = strlen s2
 then None
 else if pos >= (strlen s1) || pos >= (strlen s2)
 then Some pos
 else begin 
   if (index s1 pos) <> (index s2 pos) 
   then Some pos
   else first_diff' s1 s2 (pos+1)
 end

let first_diff s1 s2 = first_diff' s1 s2 0

let rec lines' s (upto:nat{upto <= strlen s}) 
           lastnewline lines chars (pos: nat{pos <= upto && pos <= strlen s}) :
  Tot (nat & nat) 
      (decreases upto - pos)
= if pos = upto 
  then (if lastnewline then (lines+1, chars) else (lines, chars))
  else if index s pos = '\n'  
  then lines' s upto true  lines  0 (pos + 1)
  else (if lastnewline 
        then lines' s upto false (lines+1) chars    (pos + 1)
        else lines' s upto false lines    (chars+1) (pos + 1))

///  Return the line and character upto pos counting each starting at zero.
let lines (s: string) (upto:nat{upto <= strlen s}) : Tot (nat & nat) = 
  lines' s upto false 0 0 0
  
