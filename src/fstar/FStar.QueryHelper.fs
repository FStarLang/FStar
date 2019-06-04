(* FStar.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)
#light "off"

module FStar.QueryHelper
open FStar.Range
open FStar.Util
open FStar.JsonHelper
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Interactive.CompletionTable

module U = FStar.Util
module PI = FStar.Parser.ParseIt
module DsEnv = FStar.Syntax.DsEnv
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

type position = string * int * int
type sl_reponse = { slr_name: string;
                    slr_def_range: option<Range.range>;
                    slr_typ: option<string>;
                    slr_doc: option<string>;
                    slr_def: option<string> }

let with_printed_effect_args k =
  Options.with_saved_options
    (fun () -> Options.set_option "print_effect_args" (Options.Bool true); k ())

let term_to_string tcenv t =
  with_printed_effect_args (fun () -> FStar.TypeChecker.Normalize.term_to_string tcenv t)

let sigelt_to_string se =
  with_printed_effect_args (fun () -> Syntax.Print.sigelt_to_string se)

let symlookup tcenv symbol pos_opt requested_info =
  let info_of_lid_str lid_str =
    let lid = Ident.lid_of_ids (List.map Ident.id_of_text (U.split lid_str ".")) in
    let lid = U.dflt lid <| DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid in
    try_lookup_lid tcenv lid |> U.map_option (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  let docs_of_lid lid =
    DsEnv.try_lookup_doc tcenv.dsenv lid |> U.map_option fst in

  let def_of_lid lid =
    U.bind_opt (TcEnv.lookup_qname tcenv lid) (function
      | (Inr (se, _), _) -> Some (sigelt_to_string se)
      | _ -> None) in

  let info_at_pos_opt =
    U.bind_opt pos_opt (fun (file, row, col) ->
      TcErr.info_at_pos tcenv file row col) in

  let info_opt =
    match info_at_pos_opt with
    | Some _ -> info_at_pos_opt
    | None -> if symbol = "" then None else info_of_lid_str symbol in

    match info_opt with
    | None -> None
    | Some (name_or_lid, typ, rng) ->
      let name =
        match name_or_lid with
        | Inl name -> name
        | Inr lid -> Ident.string_of_lid lid in
      let typ_str =
        if List.mem "type" requested_info then
          Some (term_to_string tcenv typ)
        else None in
      let doc_str =
        match name_or_lid with
        | Inr lid when List.mem "documentation" requested_info -> docs_of_lid lid
        | _ -> None in
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

let ck_completion (st: repl_state) (search_term: string) : list<CTable.completion_result> =
  let needle = U.split search_term "." in
  let mods_and_nss = CTable.autocomplete_mod_or_ns st.repl_names needle mod_filter in
  let lids = CTable.autocomplete_lid st.repl_names needle in
  lids @ mods_and_nss

let deflookup (env: TcEnv.env) (pos: txdoc_pos) : option<assoct> =
  match symlookup env "" (Some (pos_munge pos)) ["defined-at"] with
  | Some { slr_name = _; slr_def_range = (Some r); slr_typ = _; slr_doc = _; slr_def = _ } ->
      resultResponse (js_loclink r)
  | _ -> nullResponse

// A hover-provider provides both the type and the definition of a given symbol
let hoverlookup (env: TcEnv.env) (pos: txdoc_pos) : option<assoct> =
  match symlookup env "" (Some (pos_munge pos)) ["type"; "definition"] with
  | Some { slr_name = n; slr_def_range = _; slr_typ = (Some t); slr_doc = _; slr_def = (Some d) } ->
    let hovertxt = U.format2 "```fstar\n%s\n````\n---\n```fstar\n%s\n```" t d in
    resultResponse (JsonAssoc [("contents", JsonAssoc [("kind", JsonStr "markdown");
                                                       ("value", JsonStr hovertxt)])])
  | _ -> nullResponse

let complookup (st: repl_state) (pos: txdoc_pos) : option<assoct> =
  // current_col corresponds to the current cursor position of the incomplete identifier
  let (file, row, current_col) = pos_munge pos in
  let (Some (_, text)) = PI.read_vfs_entry file in
  // Find the column that begins a partial identifier
  let rec find_col l =
    match l with
    | [] -> 0
    | h::t -> if h = ' ' && List.length t < current_col then (List.length t + 1) else find_col t in
  let str = List.nth (U.splitlines text) (row - 1) in
  let explode s =
    let rec exp i l =
      if i < 0 then l else exp (i - 1) (String.get s i :: l) in
    exp (String.length s - 1) [] in
  let begin_col = find_col (List.rev (explode str)) in
  let term = U.substring str begin_col (current_col - begin_col) in
  let items = ck_completion st term in
  let l = List.map (fun r -> JsonAssoc [("label", JsonStr r.completion_candidate)]) items in
  resultResponse (JsonList l)