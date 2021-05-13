(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.o
*)

module Steel.FractionalPermission
open FStar.Real

[@@erasable]
noeq type perm : Type0 =
  | MkPerm: v:real{ v >. zero } -> perm

let writeable (p: perm) : GTot bool =
  MkPerm?.v p = one

let half_perm (p: perm) : Tot perm =
  MkPerm ((MkPerm?.v p) /. two)

let sum_perm (p1 p2: perm) : Tot perm =
  MkPerm (MkPerm?.v p1 +.  MkPerm?.v p2)

let lesser_equal_perm (p1 p2:perm) : GTot bool =
  MkPerm?.v p1 <=.  MkPerm?.v p2

let full_perm : perm = MkPerm one
