(*
   Copyright 2023 Microsoft Research

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

module Pulse.Syntax.Builder
open Pulse.Syntax

let pat_var s = Pat_Var s
let pat_const c = Pat_Constant c
let pat_cons fv vs = Pat_Cons fv vs

let tm_return expected_type insert_eq term = Tm_Return { expected_type; insert_eq; term }
let tm_abs b q ascription body = Tm_Abs { b; q; ascription; body }
let tm_stapp head arg_qual arg = Tm_STApp { head; arg_qual; arg }
let tm_bind binder head body = Tm_Bind { binder; head; body }
let tm_totbind binder head body = Tm_TotBind { binder; head; body }
let tm_if b then_ else_ post = Tm_If { b; then_; else_; post }
let tm_match sc returns_ brs = Tm_Match {sc; returns_; brs}
let tm_elim_exists p = Tm_ElimExists { p }
let tm_intro_exists p witnesses = Tm_IntroExists { p; witnesses }
let tm_while invariant condition condition_var body = Tm_While { invariant; condition; condition_var; body }
let tm_par pre1 body1 post1 pre2 body2 post2 = Tm_Par { pre1; body1; post1; pre2; body2; post2 }
let tm_with_inv name body returns_inv = Tm_WithInv { name; body; returns_inv }
let tm_add_inv names n r = tm_add_inv names n
let tm_with_local binder initializer body = Tm_WithLocal { binder; initializer; body }
let tm_with_local_array binder initializer length body = Tm_WithLocalArray { binder; initializer; length; body }
let tm_admit ctag u typ post = Tm_Admit { ctag; u; typ; post }
let tm_unreachable = Tm_Unreachable
let with_range t r = { term = t; range = r; effect_tag = default_effect_hint }
let tm_assert_with_binders bs p t = Tm_ProofHintWithBinders { hint_type=ASSERT { p }; binders=bs; t }
let mk_assert_hint_type p = ASSERT { p }
let mk_unfold_hint_type names p = UNFOLD { names; p }
let mk_fold_hint_type names p = FOLD { names; p }
let mk_rename_hint_type pairs goal = RENAME { pairs; goal }
let mk_rewrite_hint_type t1 t2 tac_opt = REWRITE { t1; t2; tac_opt }
let mk_fn_decl id isrec bs comp meas body : decl' = FnDecl { id; isrec; bs; comp; meas; body }
let mk_decl d range : decl = {d; range}
