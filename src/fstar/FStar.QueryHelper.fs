(* FStar.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)
#light "off"

module FStar.QueryHelper
open FStar.Range
open FStar.Util
open FStar.JsonHelper
open FStar.TypeChecker.Env

module DsEnv = FStar.Syntax.DsEnv
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env

type loc = string * int * int
type env_t = TcEnv.env
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

let run_symbol_lookup st symbol pos_opt requested_info =
  let tcenv = st.repl_env in

  let info_of_lid_str lid_str =
    let lid = Ident.lid_of_ids (List.map Ident.id_of_text (Util.split lid_str ".")) in
    let lid = Util.dflt lid <| DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid in
    try_lookup_lid tcenv lid |> Util.map_option (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  let docs_of_lid lid =
    DsEnv.try_lookup_doc tcenv.dsenv lid |> Util.map_option fst in

  let def_of_lid lid =
    Util.bind_opt (TcEnv.lookup_qname tcenv lid) (function
      | (Inr (se, _), _) -> Some (sigelt_to_string se)
      | _ -> None) in

  let info_at_pos_opt =
    Util.bind_opt pos_opt (fun (file, row, col) ->
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