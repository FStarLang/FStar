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

module PulseCore.FractionalPermission

include FStar.Real

open FStar.Real

/// This module defines fractional permissions, to be used with Steel references

/// A fractional permission is a real value between 0 (excluded) and 1.
/// 1 represents full ownership, while any fraction corresponds to a shared
/// permission.
/// Note: Does not use real literals, but rather the wrappers one, zero, two, …
/// Real literals are currently not supported by Meta-F*'s reflection framework
type perm : Type0 = r:real { r >. zero }

// /// A reference is only safely writeable if we have full permission
// let writeable (p: perm) : prop = p == one

// /// Helper around splitting a permission in half
// let half_perm (p: perm) : Tot perm = p /. two

// /// Helper to combine two permissions into one
// let sum_perm (p1 p2: perm) : Tot perm = p1 +. p2

// /// Helper to compare two permissions
// let lesser_equal_perm (p1 p2:perm) : prop = p1 <=. p2

// let lesser_perm (p1 p2:perm) : prop = p1 <. p2

// /// Wrapper around the full permission value
// let full_perm : perm = 1.0R

// /// Complement of a permission
// let comp_perm (p:perm{p `lesser_perm` full_perm}) : GTot perm =
//   1.0R -. p

// /// A convenience lemma
// let sum_halves (p:perm)
//   : Lemma (sum_perm (half_perm p) (half_perm p) == p)
//           [SMTPat (sum_perm (half_perm p) (half_perm p))]
//   = assert (forall (r:real). r /. 2.0R +. r /. 2.0R == r)

// let sum_comp (p:perm{p `lesser_perm` full_perm})
//   : Lemma (sum_perm p (comp_perm p) == full_perm)
//           [SMTPat (sum_perm p (comp_perm p))]
//   = ()

// let sum_lemma (f1 f2 : perm)
//   : Lemma (sum_perm (half_perm f1) (half_perm f2) == half_perm (sum_perm f1 f2))
//           [SMTPat (sum_perm (half_perm f1) (half_perm f2))]
//   = assert (forall x y. (x +. y) /. 2.0R == x /. 2.0R +. y /. 2.0R)
