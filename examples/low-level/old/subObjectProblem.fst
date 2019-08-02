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
type point = nat * nat

val transpose : point -> Tot point
let tr>anspose pt = (snd pt, fst pt)

val transposeST : lref point -> Mem unit ..

type robot = point * point

val rtrapose : robot -> Mem unit ..

(* here we would like to use the above trsposeST function.
but there is currently no way to get a reference to the sub object. 
the index offset and lenght trick worked for subarrays, e.g. in md5
but wont take us far. there is no simple superobject in tgis case.
a point may be embedded in all kinds of subsets.*)