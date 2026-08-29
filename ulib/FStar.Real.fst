(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Real

/// The implementation of [FStar.Real].
///
/// See the interface for the full story. In brief: the type and operations
/// declared in [FStar.Real.fsti] are mapped by F*'s SMT encoding onto Z3's
/// native theory of reals, and *here* they are simultaneously given a concrete
/// definition as the Dedekind reals of [FStar.Real.Dedekind]. This is exactly
/// the arrangement [FStar.BV] has with [FStar.BitVector]: a primitively
/// encoded interface backed by a construction.

module R = FStar.Real.Dedekind
module S = FStar.Real.Dedekind.Sqrt

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let real = R.real

let of_int (n:int) : real = R.of_int n

let ( +. ) (x y:real) : real = R.add x y
let ( -. ) (x y:real) : real = R.sub x y
let ( *. ) (x y:real) : real = R.mul x y
let ( /. ) (x:real) (d:real{d =!= 0.0R}) : real = R.div x d

let ( >.  ) (x y:real) : prop = R.gt x y
let ( >=. ) (x y:real) : prop = R.ge x y
let ( <.  ) (x y:real) : prop = R.lt x y
let ( <=. ) (x y:real) : prop = R.le x y

/// [of_int] is folded to a real literal by the normalizer whenever its
/// argument is a literal, which stops the defining equation above from firing
/// on e.g. [zero]. Stating the equation at a *variable* dodges the fold, and
/// instantiating the result at a literal then recovers the literal fact.
let of_int_eq (n:int) : Lemma (of_int n == R.of_int n) = ()

let lit_zero () : Lemma (0.0R == R.zero) = of_int_eq 0

let two_eq () : Lemma (two == R.two) = of_int_eq 2

(**** Completeness, transferred from the construction *)

/// [real] is *defined* to be [R.real], so the two notions of set-of-reals,
/// of upper bound and of least upper bound are literally the same; the only
/// content here is [R.lub] itself.

let lub (s:rset)
  : Ghost real
      (requires nonempty s /\ bounded_above s)
      (ensures  fun b -> is_lub s b)
  = R.lub s

let archimedean (x:real) : Lemma (exists (n:nat). x <. of_int n)
  = R.archimedean x;
    eliminate exists (n:nat). R.lt x (R.of_int n)
    with begin
      of_int_eq n;
      introduce exists (m:nat). x <. of_int m with n and ()
    end

(**** [sqrt_2], proved *)

let sqrt_2 : r:real{r >=. 0.0R /\ r *. r == two} =
  lit_zero ();
  two_eq ();
  S.sqrt_nonneg R.two;
  S.sqrt_two_sq ();
  S.sqrt R.two
