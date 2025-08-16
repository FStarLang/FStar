(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
module FStarC.Hooks

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Class.Show
open FStarC.Syntax.Print {}

module RE = FStarC.Reflection.V2.Embeddings

(* This is pretty awful. Now that we have Lazy_embedding, we can get rid of this table. *)
let lazy_chooser (k:Syntax.Syntax.lazy_kind) (i:Syntax.Syntax.lazyinfo) : Syntax.Syntax.term
  = match k with
    (* TODO: explain *)
    | Syntax.Syntax.BadLazy               -> failwith "lazy chooser: got a BadLazy"
    | Syntax.Syntax.Lazy_bv               -> RE.unfold_lazy_bv          i
    | Syntax.Syntax.Lazy_namedv           -> RE.unfold_lazy_namedv      i
    | Syntax.Syntax.Lazy_binder           -> RE.unfold_lazy_binder      i
    | Syntax.Syntax.Lazy_letbinding       -> RE.unfold_lazy_letbinding  i
    | Syntax.Syntax.Lazy_optionstate      -> RE.unfold_lazy_optionstate i
    | Syntax.Syntax.Lazy_fvar             -> RE.unfold_lazy_fvar        i
    | Syntax.Syntax.Lazy_comp             -> RE.unfold_lazy_comp        i
    | Syntax.Syntax.Lazy_env              -> RE.unfold_lazy_env         i
    | Syntax.Syntax.Lazy_sigelt           -> RE.unfold_lazy_sigelt      i
    | Syntax.Syntax.Lazy_universe         -> RE.unfold_lazy_universe    i

    | Syntax.Syntax.Lazy_proofstate       -> Tactics.Embedding.unfold_lazy_proofstate i
    | Syntax.Syntax.Lazy_goal             -> Tactics.Embedding.unfold_lazy_goal i

    | Syntax.Syntax.Lazy_doc              -> RE.unfold_lazy_doc i

    | Syntax.Syntax.Lazy_uvar             -> FStarC.Syntax.Util.exp_string "((uvar))"
    | Syntax.Syntax.Lazy_universe_uvar    -> FStarC.Syntax.Util.exp_string "((universe_uvar))"
    | Syntax.Syntax.Lazy_issue            -> FStarC.Syntax.Util.exp_string "((issue))"
    | Syntax.Syntax.Lazy_ident            -> FStarC.Syntax.Util.exp_string "((ident))"
    | Syntax.Syntax.Lazy_tref             -> FStarC.Syntax.Util.exp_string "((tref))"

    | Syntax.Syntax.Lazy_embedding (_, t) -> Thunk.force t
    | Syntax.Syntax.Lazy_extension s      -> FStarC.Syntax.Util.exp_string (Format.fmt1 "((extension %s))" s)

let () =
  Syntax.DsEnv.ugly_sigelt_to_string_hook := show;
  Errors.set_parse_warn_error Parser.ParseIt.parse_warn_error;
  Syntax.Syntax.lazy_chooser := Some lazy_chooser;
  Syntax.Util.tts_f := Some show;
  Syntax.Util.ttd_f := Some Class.PP.pp;
  TypeChecker.Normalize.unembed_binder_knot := Some RE.e_binder;
  iter Tactics.Interpreter.register_tactic_primitive_step Tactics.V1.Primops.ops;
  iter Tactics.Interpreter.register_tactic_primitive_step Tactics.V2.Primops.ops;
  ()
