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
module Bug815b

open FStar.List.Tot

val pop : s1:(list int){length s1 > 0} ->
  Tot (s2:(list int){length s2 = length s1 - 1})
let pop = Cons?.tl

(* This works: *)
(* let pop xs = Cons?.tl xs *)
