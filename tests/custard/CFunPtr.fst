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

(* Section 19.12.  A closed lambda is a function that was not given a name.

   [iter_t] is EverParse's [array_iterator_t] in miniature: a record of a
   value and the function pointers that interpret it.  Two ways to fill it
   in -- with the name of a top-level function, and with a lambda written
   inline -- and the only difference between them in C is whether the
   backend had a symbol to take the address of.  So [Simplify.lift_lambdas]
   makes one, and both come out as the same struct of pointers to top-level
   functions.

   The capturing case, which genuinely needs a closure and is still rejected,
   is [CNoClosure.fst]. *)
module CFunPtr

module U64 = FStar.UInt64
module I32 = FStar.Int32

noeq
type iter_t = {
  contents:      U64.t;
  impl_validate: (U64.t -> bool);
  impl_parse:    (U64.t -> U64.t);
}

let is_even (x : U64.t) : bool = U64.rem x 2uL = 0uL
let halve   (x : U64.t) : U64.t = U64.div x 2uL

(* Named functions: this shape already worked. *)
let mk_named (x : U64.t) : iter_t =
  { contents = x; impl_validate = is_even; impl_parse = halve }

(* The same record, written with lambdas.  Both are closed. *)
let mk_lambda (x : U64.t) : iter_t =
  { contents      = x;
    impl_validate = (fun y -> U64.rem y 2uL = 0uL);
    impl_parse    = (fun y -> U64.div y 2uL) }

let run (i : iter_t) : U64.t =
  if i.impl_validate i.contents then i.impl_parse i.contents else 0uL

(* A lambda in an argument position rather than a field, passed to a function
   that stores it.  Same lifting, different route to the backend. *)
let apply_twice (f : U64.t -> U64.t) (x : U64.t) : U64.t = f (f x)

let quarter (x : U64.t) : U64.t = apply_twice (fun y -> U64.div y 2uL) x

let main () : FStar.All.ML I32.t =
  let a = run (mk_named 8uL) in
  let b = run (mk_lambda 8uL) in
  let c = run (mk_lambda 7uL) in
  let d = quarter 12uL in
  if U64.eq a 4uL && U64.eq b 4uL && U64.eq c 0uL && U64.eq d 3uL
  then 0l else 1l
