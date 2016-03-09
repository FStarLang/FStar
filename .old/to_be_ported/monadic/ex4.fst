(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#monadic(DST, returnDST, composeDST)
module Ex4

val my_even : int -> bool
val my_odd : int -> bool

let rec my_even x =
  if x = 0
  then true
  else my_odd (x - 1)
and my_odd x =
  if x = 0
  then false
  else my_even (x - 1)

