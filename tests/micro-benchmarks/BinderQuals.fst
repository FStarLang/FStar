(*
   Copyright 2008-2025 Microsoft Research

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
module BinderQuals

/// Binder qualifiers are elaboration metadata, so equality of arrow types
/// must not distinguish an [Implicit] binder from a [Meta] one: both
/// elaborate to an argument with [aqual_implicit = true], and the
/// metaprogram of a [Meta] binder only says how the argument is *solved*.
///
/// All the paths that decide equality of arrows agree on this, via
/// [FStarC.Syntax.Util.bqual_compat]: the unifier ([Rel.solve_binders]),
/// the core typechecker ([Core.check_bqual]), the definition checker
/// ([TcTerm]) and the syntactic fast path ([TermEqAndSimplify.eq_tm]).

open FStar.Tactics.Typeclasses

class def_c (a:Type) = { def : a }

instance _ : def_c int = { def = 0 }

(* [def] has type [#a:Type -> #[tcresolve ()] _:def_c a -> a]: typeclass method
   types carry a Meta binder for the class argument, since [mk_class] builds
   them with [binder_set_meta]. Here it is passed where an arrow with a plain
   Implicit binder is expected. *)
let apply_meta_as_implicit (g : (#a:Type -> #_:def_c a -> a)) : int =
  g #int #solve

let _ : int = apply_meta_as_implicit def

(* The same, but with the arrows appearing as arguments of a matching head.
   This goes through a different path in the unifier, which used to ignore
   binder qualifiers entirely. *)
let meta_as_implicit_under_ctor (l : list (#a:Type -> #[tcresolve ()] _:def_c a -> a))
  : list (#a:Type -> #_:def_c a -> a) = l

(* Two Meta binders are compatible even when their metaprograms differ: we
   never compare the metaprograms. *)
let distinct_metaprograms (f : (#[FStar.Tactics.exact (`0)] x:int -> int))
  : (#[FStar.Tactics.exact (`1)] x:int -> int) = f

(* But Implicit/Meta are still distinct from Explicit, including when the
   arrows appear under a type constructor. This last case regressed for a
   while: [eq_tm] compared the two [list] arguments while ignoring binder
   qualifiers, and reported them equal. *)
[@@expect_failure]
let implicit_is_not_explicit (f : (#x:int -> int)) : (x:int -> int) = f

[@@expect_failure]
let implicit_is_not_explicit_under_ctor (l : list (#x:int -> int))
  : list (x:int -> int) = l

[@@expect_failure]
let meta_is_not_explicit_under_ctor (l : list (#[FStar.Tactics.exact (`0)] x:int -> int))
  : list (x:int -> int) = l
