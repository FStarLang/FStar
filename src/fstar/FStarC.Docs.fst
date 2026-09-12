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

(* Documentation that says nothing and no documentation at all are the
   same fact about a declaration: no author writes a doc attribute
   meaning "the text here is empty". A consumer forced to tell the two
   apart gets it wrong in a way that matters -- the IDE answering
   [Some ""] to a lookup, and a generator rendering an empty
   documentation block, are the same mistake -- and worse, an agent
   handed an empty string reads the slot as filled and describes the
   declaration in the author's voice. So a blank payload is normalized
   here, once, rather than defended against in each consumer.

   Blank lines *within* a doc are untouched: those separate paragraphs,
   and only arise where there is text to separate. *)
let is_blank (lines : list string) : ML bool =
  lines |> for_all (fun l -> BU.trim_string l = "")

let doc_of_attrs (attrs : list S.attribute) : ML doc_status =
  match U.get_attribute PC.doc_attr attrs with
  | None -> Doc_absent
  | Some [(payload, _)] -> (
    match doc_lines payload with
    | Some lines -> if is_blank lines then Doc_absent else Doc_text lines
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
let docs_schema_version = 3

(* A declaration we export: its kind, name, elaborated type, and -- for a
   constructor -- the type it constructs. *)
type decl_info = {
  di_kind   : string;
  di_lid    : Ident.lident;
  di_typ    : S.term;
  di_parent : option Ident.lident;
}

(* The exported view of a top-level declaration, when it is one we
   export. Returns None for everything else: pragmas, effect
   declarations, splices, bundles (which are recursed into by the
   caller), and mutually recursive lets, whose single attribute list
   cannot be attributed to one of the names. *)
let decl_info_of (se : S.sigelt) : ML (option decl_info) =
  let mk k lid t p = Some { di_kind = k; di_lid = lid; di_typ = t; di_parent = p } in
  match se.sigel with
  | Sig_declare_typ {lid; t} -> mk "val" lid t None
  | Sig_let {lbs=(_, [lb])} -> (
    match lb.lbname with
    | Inr fv -> mk "let" fv.fv_name lb.lbtyp None
    | Inl _ -> None
  )
  | Sig_inductive_typ {lid; params; t} ->
    let sigt = if Nil? params then t else U.arrow params (S.mk_Total t) in
    mk "type" lid sigt None
  | Sig_datacon {lid; t; ty_lid} -> mk "constructor" lid t (Some ty_lid)
  | Sig_assume {lid; phi} -> mk "assume" lid phi None
  | _ -> None

(* The elaborated type of a declaration as a tree, so that a consumer can
   index and link it without re-parsing printed text. Every name is fully
   qualified, and binders are opened so that bound occurrences carry the
   binder's name. Nothing here interprets F*: an effect is just its name
   and its arguments, whether it is Tot, Lemma, or Pulse's stt. Terms of
   a shape a type rarely has are given as printed text. *)
let str_of_id (i : Ident.ident) : string = Ident.string_of_id i

let json_of_bqual (q : S.bqual) : json =
  match q with
  | None -> JsonStr "explicit"
  | Some (Implicit _) -> JsonStr "implicit"
  | Some (Meta _) -> JsonStr "meta"
  | Some Equality -> JsonStr "equality"

let rec json_of_term (t : S.term) : ML json =
  let t = SS.compress (U.unascribe (U.unmeta (SS.compress t))) in
  match t.n with
  | Tm_fvar fv ->
    JsonAssoc [("k", JsonStr "fv"); ("n", JsonStr (Ident.string_of_lid fv.fv_name))]
  | Tm_uinst (hd, _) -> json_of_term hd
  | Tm_name bv
  | Tm_bvar bv ->
    JsonAssoc [("k", JsonStr "var"); ("n", JsonStr (str_of_id bv.ppname))]
  | Tm_type _ -> JsonAssoc [("k", JsonStr "type")]
  | Tm_constant _ -> JsonAssoc [("k", JsonStr "const"); ("v", JsonStr (show t))]
  | Tm_app {hd; args} ->
    JsonAssoc [
      ("k", JsonStr "app");
      ("f", json_of_term hd);
      ("args", JsonList (args |> List.map (fun (a, q) ->
                  JsonAssoc [("t", json_of_term a);
                             ("imp", JsonBool (S.is_aqual_implicit q))])));
    ]
  | Tm_arrow {bs; comp} ->
    let bs, c = SS.open_comp bs comp in
    JsonAssoc [
      ("k", JsonStr "arrow");
      ("bs", JsonList (List.map json_of_binder bs));
      ("c", json_of_comp c);
    ]
  | Tm_refine {b; phi} ->
    let bs, phi = SS.open_term [S.mk_binder b] phi in
    let b = (List.hd bs).binder_bv in
    JsonAssoc [
      ("k", JsonStr "refine");
      ("x", JsonStr (str_of_id b.ppname));
      ("t", json_of_term b.sort);
      ("phi", json_of_term phi);
    ]
  | Tm_abs {bs; body} ->
    let bs, body = SS.open_term bs body in
    JsonAssoc [
      ("k", JsonStr "abs");
      ("bs", JsonList (List.map json_of_binder bs));
      ("body", json_of_term body);
    ]
  | _ -> JsonAssoc [("k", JsonStr "other"); ("s", JsonStr (show t))]

and json_of_binder (b : S.binder) : ML json =
  JsonAssoc [
    ("x", JsonStr (str_of_id b.binder_bv.ppname));
    ("q", json_of_bqual b.binder_qual);
    ("t", json_of_term b.binder_bv.sort);
  ]

and json_of_comp (c : S.comp) : ML json =
  let eff, res, args =
    match c.n with
    | Total t -> "Prims.Tot", t, []
    | GTotal t -> "Prims.GTot", t, []
    | Comp ct ->
      Ident.string_of_lid ct.effect_name, ct.result_typ, List.map fst ct.effect_args
  in
  JsonAssoc [
    ("eff", JsonStr eff);
    ("res", json_of_term res);
    ("args", JsonList (List.map json_of_term args));
  ]

(* The fully qualified names a term mentions, for linking. *)
let refs_of (ts : list S.term) : ML (list string) =
  ts
  |> List.collect (fun t -> FStarC.Class.Setlike.elems (FStarC.Syntax.Free.fvars t))
  |> List.map Ident.string_of_lid
  |> BU.remove_dups (fun a b -> a = b)

(* The definition of a transparent let, when its body is part of what
   the declaration means to a reader: a specification such as `sorted`
   is its body. Lemma proofs are not, and are left out. *)
let definition_of (se : S.sigelt) : ML (option S.term) =
  match se.sigel with
  | Sig_let {lbs=(_, [lb])} ->
    if U.is_lemma lb.lbtyp
    || se.sigquals |> List.existsb (function Irreducible -> true | _ -> false)
    then None
    else Some lb.lbdef
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

let doc_lines_of (se : S.sigelt) : ML (option (list string)) =
  match doc_of_sigelt se with
  | Doc_absent -> None
  | Doc_unsupported payload ->
    Errors.log_issue se.sigrng Errors.Warning_UnrecognizedAttribute [
      Errors.Msg.text "Ignoring a 'doc' attribute whose payload is not a literal list of string literals.";
      Errors.Msg.text (Format.fmt1 "Payload: %s" payload);
    ];
    None
  | Doc_text lines -> Some lines

(* The text of [r] in a source file given as its lines. Ranges count
   lines from 1 and columns from 0. *)
let snippet (lines : list string) (r : Range.range) : ML (option string) =
  let s = start_of_range r in
  let e = end_of_range r in
  let l0 = line_of_pos s in
  let l1 = line_of_pos e in
  if l0 < 1 || l1 < l0 || l1 > List.length lines then None
  else
    let rec take (i : int) (ls : list string) : ML (list string) =
      match ls with
      | [] -> []
      | l :: ls ->
        if i > l1 then []
        else if i < l0 then take (i + 1) ls
        else
          let l = if i = l1 && col_of_pos e <= String.length l
                  then String.substring l 0 (col_of_pos e) else l in
          let l = if i = l0 && col_of_pos s <= String.length l
                  then String.substring l (col_of_pos s) (String.length l - col_of_pos s) else l in
          l :: take (i + 1) ls
    in
    Some (String.concat "\n" (take 1 lines))

let opt (#a:Type) (f : a -> ML json) (o : option a) : ML json =
  match o with Some x -> f x | None -> JsonNull

(* Every exported declaration is reported, documented or not: a reader
   needs to see the whole public surface, and an undocumented entry is
   also what a coverage report counts. A `val` and the `let` that
   defines it are one declaration: the `val` gives the signature the
   author wrote, and its documentation if it has any; the `let` supplies
   the definition. *)
let rec json_of_sigelt (src : option (list string))
                       (find_let : Ident.lident -> ML (option S.sigelt))
                       (has_val : Ident.lident -> ML bool)
                       (se : S.sigelt) : ML (list json) =
  match se.sigel with
  (* A bundle is not itself a declaration; its members are. *)
  | Sig_bundle {ses} -> List.collect (json_of_sigelt src find_let has_val) ses
  | _ ->
    if not (is_exported se) then []
    else
      match decl_info_of se with
      | None -> []
      | Some di when di.di_kind = "let" && has_val di.di_lid -> []
      | Some di ->
        let defn_se = if di.di_kind = "val" then find_let di.di_lid else Some se in
        let doc =
          match doc_lines_of se, defn_se with
          | Some lines, _ -> Some lines
          | None, Some lse when di.di_kind = "val" -> doc_lines_of lse
          | None, _ -> None
        in
        let defn = match defn_se with Some lse -> definition_of lse | None -> None in
        [JsonAssoc [
          ("name",       JsonStr (Ident.string_of_lid di.di_lid));
          ("kind",       JsonStr di.di_kind);
          ("parent",     opt (fun l -> JsonStr (Ident.string_of_lid l)) di.di_parent);
          ("signature",  JsonStr (show di.di_typ));
          ("type",       json_of_term di.di_typ);
          ("definition", opt (fun d -> JsonStr (show d)) defn);
          ("refs",       JsonList (List.map JsonStr
                           (refs_of (di.di_typ :: (match defn with Some d -> [d] | None -> [])))));
          ("range",      json_of_range se.sigrng);
          (* The declaration and its definition as written, when the
             source file is at hand and is the one that was checked. *)
          ("source",     opt JsonStr (match src with
                                      | Some ls -> snippet ls se.sigrng
                                      | None -> None));
          ("definition_source",
                         opt JsonStr (match src, defn, defn_se with
                                      | Some ls, Some _, Some lse -> snippet ls lse.sigrng
                                      | _ -> None));
          ("doc",        opt (fun lines -> JsonList (List.map JsonStr lines)) doc);
        ]]

let json_of_modul_with_source (src : option (list string)) (m : S.modul) : ML json =
  let rec flatten (ses : list S.sigelt) : ML (list S.sigelt) =
    ses |> List.collect (fun se ->
      match se.sigel with
      | Sig_bundle {ses} -> flatten ses
      | _ -> [se]) in
  let ses = flatten m.declarations in
  let find_let (l : Ident.lident) : ML (option S.sigelt) =
    BU.find_map ses (fun se ->
      match se.sigel with
      | Sig_let {lbs=(_, [lb])} ->
        (match lb.lbname with
         | Inr fv when Ident.lid_equals fv.fv_name l -> Some se
         | _ -> None)
      | _ -> None) in
  let has_val (l : Ident.lident) : ML bool =
    ses |> List.existsb (fun se ->
      match se.sigel with
      | Sig_declare_typ {lid} -> Ident.lid_equals lid l
      | _ -> false) in
  JsonAssoc [
    ("schema",       JsonStr docs_schema_name);
    ("version",      JsonInt docs_schema_version);
    ("module",       JsonStr (Ident.string_of_lid m.name));
    ("interface",    JsonBool m.is_interface);
    ("declarations", JsonList (List.collect (json_of_sigelt src find_let has_val) m.declarations));
  ]

let json_of_modul (m : S.modul) : ML json = json_of_modul_with_source None m

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

(* The lines of the source file [m] was checked from, found on the
   include path, provided its digest is the one recorded in the checked
   file: a snippet of any other file could misquote the declaration. *)
let source_lines (m : S.modul) (digest : string) : ML (option (list string)) =
  let base = Ident.string_of_lid m.name ^ (if m.is_interface then ".fsti" else ".fst") in
  match Find.find_file base with
  | Some fn when BU.digest_of_file fn = digest -> Some (BU.file_get_lines fn)
  | _ -> None

let print_module (m : S.modul) (digest : string) : ML unit =
  Format.print1 "%s\n" (string_of_json (json_of_modul_with_source (source_lines m digest) m))

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
  | Some (source_digest, deps, tcr) ->
    let m = tcr.CF.checked_module in
    if m.is_interface || not (tcr.CF.has_interface)
    then print_module m source_digest
    else
      match interface_path path, recorded_interface_digest deps with
      | Some iface, Some expected_digest ->
        (match CF.load_tc_result_with_digest iface with
         | Some (iface_digest, _, iface_tcr) ->
           let iface_m = iface_tcr.CF.checked_module in
           if iface_digest = expected_digest
              && iface_m.is_interface
              && Ident.lid_equals iface_m.name m.name
           then print_module iface_m iface_digest
           else fail_missing_interface iface
         | None -> fail_missing_interface iface)
      | _ -> fail_missing_interface path
