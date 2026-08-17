(*
   Copyright 2019 Microsoft Research

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

(* FStarC.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)

module FStarC.Interactive.QueryHelper
open FStarC.Interactive.Ide.Types
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Range
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Interactive.JsonHelper
open FStarC.Interactive.CompletionTable

module U = FStarC.Util
module DsEnv = FStarC.Syntax.DsEnv
module TcErr = FStarC.TypeChecker.Err
module TcEnv = FStarC.TypeChecker.Env
module CTable = FStarC.Interactive.CompletionTable
module Overload = FStarC.TypeChecker.Overload

let with_printed_effect_args #a (k : unit -> ML a) : ML a =
  Options.with_saved_options
    (fun () -> Options.set_option "print_effect_args" (Options.Bool true); k ())

let term_to_string tcenv t =
  with_printed_effect_args (fun () -> Syntax.Print.term_to_string' (DsEnv.set_current_module tcenv.dsenv tcenv.curmodule) t)

let sigelt_to_string tcenv se =
  with_printed_effect_args (fun () -> Syntax.Print.sigelt_to_string' (DsEnv.set_current_module tcenv.dsenv tcenv.curmodule) se)

let symlookup tcenv symbol pos_opt requested_info =
  let lid_of_str lid_str =
    Ident.lid_of_ids (List.map Ident.id_of_text (U.split lid_str ".")) in

  let info_of_lid_str lid_str =
    let lid = lid_of_str lid_str in
    let lid = Option.dflt lid <| DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid in
    try_lookup_lid tcenv lid |> Option.map (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  (* Everything a bare symbol could denote, when it denotes more than one
     thing; empty when the name is not overloaded. Resolving a symbol from its
     text alone has no term, no arguments and no expected type, so there is
     nothing for type-based overload resolution to work with and
     [info_of_lid_str] can only answer with what scope order gives, which is
     the innermost binding. Whenever this list is non-empty that answer is a
     guess, and the occurrence being asked about may well denote another
     candidate. *)
  let overload_candidates lid_str =
    DsEnv.try_lookup_lid_alternatives tcenv.dsenv (lid_of_str lid_str) in

  let docs_of_lid lid = None in

  let def_of_lid lid =
    Option.bind (TcEnv.lookup_qname tcenv lid) (function
      | (Inr (se, _), _) -> Some (sigelt_to_string tcenv se)
      | _ -> None) in

  let info_at_pos_opt =
    Option.bind pos_opt (fun (file, row, col) ->
      match TcErr.info_at_pos tcenv file row col with
      | Some info -> Some info
      | None ->
        (* The identifier-info table is keyed by the file name as it appears in
           ranges, which is a basename. Clients are not obliged to send one:
           fstar-mode sends the name it was given, while the VS Code extension
           sends an absolute path or a "file://" URI. Neither of those matches,
           so without this every lookup from that client misses the table and
           is answered by the scope-order fallback below -- which for an
           overloaded name is the wrong candidate. Retrying on the basename
           accepts all three forms; [basename] also strips a URI scheme, since
           it keeps only what follows the last separator. *)
        let base = Filepath.basename file in
        if base = file then None
        else TcErr.info_at_pos tcenv base row col) in

  (* [info_at_pos] reports the name the typechecker resolved the occurrence
     to, so it is exact and needs no caveat. It answers only for a position
     that lies on an identifier in a fragment that has been checked; every
     other lookup, including one whose position is a column off the symbol,
     falls through to the guess. *)
  let info_opt, ovl_candidates =
    match info_at_pos_opt with
    | Some _ -> info_at_pos_opt, []
    | None ->
      if symbol = "" then None, []
      else info_of_lid_str symbol, overload_candidates symbol in

    match info_opt with
    | None -> None
    | Some (name_or_lid, typ, rng) ->
      let name =
        match name_or_lid with
        | Inl name -> name
        | Inr lid -> Ident.string_of_lid lid in
      let str_of_opt = function
        | None -> "<none>"
        | Some s -> s in
      let typ_str =
        if List.mem "type" requested_info then
          Some (term_to_string tcenv typ)
        else None in
      let doc_str =
        (* The caveat is not documentation of the symbol but a statement about
           how far this answer can be trusted, so it is reported whether or not
           documentation was requested: a client that asked only for the type
           is exactly the one being told something that may not hold. *)
        match ovl_candidates with
        | []
        | [_] ->
          (match name_or_lid with
           | Inr lid when List.mem "documentation" requested_info -> docs_of_lid lid
           | _ -> None)
        | _ ->
          let cands =
            Overload.candidates_doc tcenv ovl_candidates
            |> List.map Errors.Msg.renderdoc in
          Some (String.concat "\n"
                  ("This name is overloaded, and the answer above is only what scope \
                    order gives. Which candidate an occurrence denotes is decided by \
                    typechecking it, so ask again at the exact position of the \
                    occurrence once its definition has been checked. Candidates:"
                   :: cands)) in
      let def_str =
        match name_or_lid with
        | Inr lid when List.mem "definition" requested_info -> def_of_lid lid
        | _ -> None in
      let def_range =
        if List.mem "defined-at" requested_info then Some rng else None in
      Some ({ slr_name = name; slr_def_range = def_range;
             slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str })

let mod_filter = function
  | _, CTable.Namespace _
  | _, CTable.Module { CTable.mod_loaded = true } -> None
  | pth, CTable.Module md ->
    Some (pth, CTable.Module ({ md with CTable.mod_name = CTable.mod_name md ^ "." }))

let ck_completion (st: repl_state) (search_term: string) : ML (list CTable.completion_result) =
  let needle = U.split search_term "." in
  let mods_and_nss = CTable.autocomplete_mod_or_ns st.repl_names needle mod_filter in
  let lids = CTable.autocomplete_lid st.repl_names needle in
  lids @ mods_and_nss