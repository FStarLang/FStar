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

module FStarC.Docs

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Json
open FStarC.Class.Show
open FStarC.Syntax.Syntax
open FStarC.Range.Ops

module S  = FStarC.Syntax.Syntax
module U  = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module PC = FStarC.Parser.Const
module BU = FStarC.Util
module CF = FStarC.CheckedFiles

(* Opened for the showable instances of terms and sigelts. *)
open FStarC.Syntax.Print

(* Attributes are typechecked, but they are *not* normalized before the
   sigelt is serialized into a checked module: `[@@doc [a ^ b]]` is
   recorded with the unevaluated application still inside the list. So
   the only payload we can read back is a literal list of literal
   strings, and anything else has to be reported rather than silently
   guessed at. Metadata wrappers (and ascriptions, which elaboration can
   introduce) are not part of the payload, so they are peeled first.

   The list is a `Prims.Cons`/`Prims.Nil` spine. Its type argument is
   implicit, and because an attribute is not required to be a
   type-correct term it may or may not have been elaborated, so both
   shapes are accepted. FStarC.TypeChecker.DeferredImplicits reads a
   list of strings out of an attribute the same way, for the same
   reason. *)
let rec doc_lines (e : S.term) : ML (option (list string)) =
  let head, args = U.head_and_args_full (U.unascribe (U.unmeta e)) in
  match (U.un_uinst head).n, args with
  | Tm_fvar fv, _ when fv_eq_lid fv PC.nil_lid -> Some []
  | Tm_fvar fv, [_; (hd, _); (tl, _)]
  | Tm_fvar fv, [(hd, _); (tl, _)]
    when fv_eq_lid fv PC.cons_lid -> (
    match (SS.compress (U.unascribe (U.unmeta hd))).n with
    | Tm_constant (FStarC.Const.Const_string (s, _)) -> (
      match doc_lines tl with
      | None -> None
      | Some tl -> Some (s :: tl)
    )
    | _ -> None
  )
  | _ -> None

let doc_of_attrs (attrs : list S.attribute) : ML doc_status =
  match U.get_attribute PC.doc_attr attrs with
  | None -> Doc_absent
  | Some [(payload, _)] -> (
    match doc_lines payload with
    | Some lines -> Doc_text lines
    | None -> Doc_unsupported (show payload)
  )
  | Some args ->
    Doc_unsupported (Format.fmt1 "doc applied to %s arguments" (show (List.length args)))

let doc_of_sigelt (se : S.sigelt) : ML doc_status =
  if se.sigmeta.sigmeta_spliced
  || (se.sigquals |> List.existsb (function
      | Discriminator _
      | Projector _
      | OnlyName -> true
      | _ -> false))
  then Doc_absent
  else match se.sigel with
  (* See the interface: a data constructor inherits the attributes of
     its type, and we never report those as the constructor's own. *)
  | Sig_datacon _ -> Doc_absent
  | Sig_let {lbs=(_, [lb])} -> (
    (* `[@@doc "..."] let f = e` records the attribute on the sigelt;
       the letbinding is checked too so that a doc survives whichever
       of the two the desugarer chose. *)
    match doc_of_attrs se.sigattrs with
    | Doc_absent -> doc_of_attrs lb.lbattrs
    | r -> r
  )
  | _ -> doc_of_attrs se.sigattrs

let docs_schema_name = "fstar-module-docs"
let docs_schema_version = 2

(* The name, kind and printed signature of a top-level declaration, when
   it is one we export. Returns None for everything else: pragmas,
   effect declarations, splices, bundles (which are recursed into by the
   caller), and mutually recursive lets, whose single attribute list
   cannot be attributed to one of the names. *)
let decl_info (se : S.sigelt) : ML (option (string & Ident.lident & string)) =
  match se.sigel with
  | Sig_declare_typ {lid; t} ->
    Some ("val", lid, show t)
  | Sig_let {lbs=(_, [lb])} -> (
    match lb.lbname with
    | Inr fv -> Some ("let", fv.fv_name, show lb.lbtyp)
    | Inl _ -> None
  )
  | Sig_inductive_typ {lid; params; t} ->
    let sigt = if Nil? params then t else U.arrow params (S.mk_Total t) in
    Some ("type", lid, show sigt)
  | Sig_assume {lid; phi} ->
    Some ("assume", lid, show phi)
  | _ -> None

(* Whether a declaration is part of what the module exports, and was
   written by the user.

   The second half matters for documentation specifically. Checking an
   inductive type definition generates a discriminator for each of its
   constructors, and a projector for each of their arguments, and each
   of those generated declarations inherits the *type's* attribute list
   -- including its documentation. Reporting the type's text under
   'uu___is_Red' would be nonsense, so generated declarations are
   dropped here, just as data constructors are dropped in
   [doc_of_sigelt]. Documenting constructors, projectors and fields is
   out of scope. *)
let is_exported (se : S.sigelt) : ML bool =
  if se.sigmeta.sigmeta_spliced then false
  else
    se.sigquals |> for_all (fun q ->
      match q with
      | Private
      | Discriminator _
      | Projector _
      | OnlyName
      | InternalAssumption -> false
      | _ -> true)

let json_of_range (r : Range.range) : ML json =
  if file_of_range r = "dummy" then JsonNull
  else
    let s = start_of_range r in
    let e = end_of_range r in
    JsonAssoc [
      ("file",       JsonStr (Filepath.basename (file_of_range r)));
      ("start_line", JsonInt (line_of_pos s));
      ("start_col",  JsonInt (col_of_pos s));
      ("end_line",   JsonInt (line_of_pos e));
      ("end_col",    JsonInt (col_of_pos e));
    ]

let rec json_of_sigelt (se : S.sigelt) : ML (list json) =
  match se.sigel with
  (* A bundle is not itself a declaration; its members are. *)
  | Sig_bundle {ses} -> List.collect json_of_sigelt ses
  | _ ->
    if not (is_exported se) then []
    else
      match doc_of_sigelt se, decl_info se with
      | Doc_absent, _ -> []
      | Doc_unsupported payload, _ ->
        Errors.log_issue se.sigrng Errors.Warning_UnrecognizedAttribute [
          Errors.Msg.text "Ignoring a 'doc' attribute whose payload is not a literal list of string literals.";
          Errors.Msg.text (Format.fmt1 "Payload: %s" payload);
        ];
        []
      | Doc_text _, None -> []
      | Doc_text lines, Some (kind, lid, sigstr) ->
        [JsonAssoc [
          ("name",      JsonStr (Ident.string_of_lid lid));
          ("kind",      JsonStr kind);
          ("signature", JsonStr sigstr);
          ("range",     json_of_range se.sigrng);
          ("doc",       JsonList (List.map JsonStr lines));
        ]]

let json_of_modul (m : S.modul) : ML json =
  JsonAssoc [
    ("schema",       JsonStr docs_schema_name);
    ("version",      JsonInt docs_schema_version);
    ("module",       JsonStr (Ident.string_of_lid m.name));
    ("interface",    JsonBool m.is_interface);
    ("declarations", JsonList (List.collect json_of_sigelt m.declarations));
  ]

let interface_path (path : string) : ML (option string) =
  let suf = ".fst.checked" in
  if BU.ends_with path suf then
    let stem = String.substring path 0 (String.length path - String.length suf) in
    Some (stem ^ ".fsti.checked")
  else None

let fail_missing_interface (path : string) : ML unit =
  let open FStarC.Pprint in
  Errors.raise_error0 Errors.Fatal_ModuleOrFileNotFound [
    Errors.Msg.text "The implementation was checked against an interface, but its authoritative checked interface could not be loaded from:";
    doc_of_string path;
  ]

let print_module (m : S.modul) : ML unit =
  Format.print1 "%s\n" (string_of_json (json_of_modul m))

let recorded_interface_digest (deps : list (string & string)) : ML (option string) =
  match deps with
  | ("source", _) :: ("interface", digest) :: _ -> Some digest
  | _ -> None

let export_docs (path : string) : ML unit =
  match CF.load_tc_result_with_digest path with
  | None ->
    let open FStarC.Pprint in
    Errors.raise_error0 Errors.Fatal_ModuleOrFileNotFound [
      Errors.Msg.text "Could not read checked file:" ^/^ doc_of_string path
    ]
  | Some (_source_digest, deps, tcr) ->
    let m = tcr.CF.checked_module in
    if m.is_interface || not (tcr.CF.has_interface)
    then print_module m
    else
      match interface_path path, recorded_interface_digest deps with
      | Some iface, Some expected_digest ->
        (match CF.load_tc_result_with_digest iface with
         | Some (actual_digest, _, iface_tcr) ->
           let iface_m = iface_tcr.CF.checked_module in
           if actual_digest = expected_digest
              && iface_m.is_interface
              && Ident.lid_equals iface_m.name m.name
           then print_module iface_m
           else fail_missing_interface iface
         | None -> fail_missing_interface iface)
      | _ -> fail_missing_interface path
