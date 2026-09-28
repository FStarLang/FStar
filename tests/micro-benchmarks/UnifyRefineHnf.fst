(*
   Copyright 2008-2026 Microsoft Research

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
module UnifyRefineHnf

(* Rel decides an equation it cannot solve syntactically by reducing both
   sides and recursing.  The reduction has to go under a refinement's
   formula: [refine (in_bounds n)] is [x:nat{in_bounds n x == true}] and
   [bounded n] is [x:nat{in_bounds n x}], and relating the two formulas
   needs [in_bounds] unfolded on both sides.  A *weak* head reduction stops
   before that, so the equation is left to the SMT solver, which cannot
   prove two types equal. *)

let refine (#t:Type) (f: t -> GTot bool) = (x:t { f x == true })

assume val parser : Type -> Type0

assume val mk_filter (#t:Type) (f: t -> GTot bool) : parser (refine f)

let in_bounds (n:nat) (x:nat) : GTot bool = x <= n

let bounded (n:nat) = (x:nat { in_bounds n x })

let test (n:nat) : parser (bounded n) = mk_filter (in_bounds n)
