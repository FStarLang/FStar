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
   limitations under the License.
*)

module Steel.FractionalPermission
open FStar.Real

/// This module defines fractional permissions, to be used with Steel references

/// A fractional permission is a real value between 0 (excluded) and 1.
/// 1 represents full ownership, while any fraction corresponds to a shared
/// permission.
/// Note: Does not use real literals, but rather the wrappers one, zero, two, …
/// Real literals are currently not supported by Meta-F*'s reflection framework
[@@erasable]
noeq type perm : Type0 =
  | MkPerm: v:real{ v >. zero } -> perm

/// A reference is only safely writeable if we have full permission
let writeable (p: perm) : GTot bool =
  MkPerm?.v p = one

/// Helper around splitting a permission in half
let half_perm (p: perm) : Tot perm =
  MkPerm ((MkPerm?.v p) /. two)

/// Helper to combine two permissions into one
let sum_perm (p1 p2: perm) : Tot perm =
  MkPerm (MkPerm?.v p1 +.  MkPerm?.v p2)

/// Helper to compare two permissions
let lesser_equal_perm (p1 p2:perm) : GTot bool =
  MkPerm?.v p1 <=.  MkPerm?.v p2

/// Wrapper around the full permission value
let full_perm : perm = MkPerm one

/// A convenience lemma
let sum_halves (p:perm)
  : Lemma (sum_perm (half_perm p) (half_perm p) == p)
          [SMTPat (sum_perm (half_perm p) (half_perm p))]
  = assert (forall (r:real). r /. 2.0R +. r /. 2.0R == r)
