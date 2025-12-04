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

module PulseSyntaxExtension.Printing

open FStarC
open FStarC.Effect

module SW = PulseSyntaxExtension.SyntaxWrapper
module A = FStarC.Parser.AST
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module DsEnv = FStarC.Syntax.DsEnv

open FStarC.Syntax.Syntax
open FStarC.Syntax.Resugar
open FStarC.Class.Show
open FStarC.Class.PP
open PulseSyntaxExtension.Env
open FStarC.Pprint

let hua (t:term) : option (S.fv & list S.universe & S.args) =
  let t = U.unmeta t in
  let hd, args = U.head_and_args_full t in
  let hd = U.unmeta hd in
  match (SS.compress hd).n with
  | Tm_fvar fv -> Some (fv, [], args)
  | Tm_uinst ({ n = Tm_fvar fv }, us) -> Some (fv, us, args)
  | _ -> None

let p = FStarC.Parser.ToDocument.term_to_document

let vconcat (ds:list document) : document =
  match ds with
  | h::t ->
    List.fold_left (fun l r -> if r = empty then l else l ^^ hardline ^^ r) h t
  | [] ->
    empty

let print_pulse_computation_type
  (rng : Range.t)
  (e : DsEnv.env)
  (tag : string)
  (a opens pre post : term)
  : A.term
  =
  let retname_opt, post =
    match U.abs_formals post with
    | [b], t, _ ->
      let bv = b.binder_bv in
      if FStarC.Class.Setlike.mem bv (Syntax.Free.names t) then
        Some b.binder_bv, t
      else
        None, t
    | _ ->
      // If it returns unit, just apply the post to `()`
      if U.term_eq a S.t_unit then
        None, U.mk_app post [S.as_arg U.exp_unit]
      else
        let x = S.gen_bv "_ret" (Some rng) a in
        Some x, U.mk_app post [S.as_arg (S.bv_to_name x)]
  in
  let d =
    align <| hang 2 <| vconcat <| List.map (fun d -> group (hang 2 d)) [
      (if tag <> ""
        then doc_of_string tag ^/^ doc_of_string "fn"
        else doc_of_string "fn");
      doc_of_string "requires" ^/^ p (resugar_term' e pre);
      (if U.term_eq opens SW.tm_emp_inames then empty
       else
        (doc_of_string "opens"    ^/^ p (resugar_term' e opens)));
      (match retname_opt with
       | None when U.term_eq a S.t_unit -> empty
       | None ->
        doc_of_string "returns" ^/^ p (resugar_term' e a)
       | Some bv ->
        doc_of_string "returns"  ^/^ pp bv.ppname ^/^ colon ^/^ p (resugar_term' e a));
      doc_of_string "ensures"  ^/^ p (resugar_term' e post);
    ]
  in
  A.mk_term (A.LitDoc d) rng A.Expr

let resugar_pulse_type (e:DsEnv.env) (t:S.term) : A.term =
  let r = hua t in
  if None? r then raise SkipResugar;
  let Some (fv, us, args) = r in
  let tag, a, opens, pre, post =
    match args with
    | [(a, None); (pre, None); (post, None)]
      when S.fv_eq_lid fv stt_lid ->
        ("", a, SW.tm_emp_inames, pre, post)

    | [(a, None); _obs; (opens, None); (pre, None); (post, None)]
      when S.fv_eq_lid fv stt_atomic_lid ->
        ("atomic", a, opens, pre, post)

    | [(a, None); (opens, None); (pre, None); (post, None)]
      when S.fv_eq_lid fv stt_ghost_lid ->
        ("ghost", a, opens, pre, post)

    | _ -> raise SkipResugar
  in
  print_pulse_computation_type (pos t) e tag a opens pre post

let _ = register_pass resugar_pulse_type
