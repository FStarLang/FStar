(* This is a tiny toy language extension for F*.
  It's deliberately different from F* syntax -- we want to be able to test top level module declarations.
  We want to test inter-module dependencies, so we have a simple expression language with qualified identifiers
  and integer literals.

  Grammar:

    DECL ::=
      | "module:" QID
      | "let:" ID ":" EXPR
      | "comment:" ...

    EXPR ::=
      | QID | INTLIT
*)
(* I wrote this in OCaml to avoid needing to extract ... maybe bad idea *)
open Fstarcompiler
open FStar_Pervasives

module I    = FStarC_Ident
module FPA  = FStarC_Parser_AST
module FPAU = FStarC_Parser_AST_Util

let take_prefix (prefix: string) (s: string) =
  if String.starts_with ~prefix s then
    Some (String.sub s (String.length prefix) (String.length s - String.length prefix))
  else
    None

let err str r = Inl { FPAU.message = [(*TODO*)]; FPAU.range = r }

let mk_ident (id_str: string) (r: FStarC_Range.t): I.ident =
  I.mk_ident (id_str, r)

let mk_lident (id_str: string) (r: FStarC_Range.t): I.lident =
  I.lid_of_str id_str

let parse_let (contents: string) (r: FStarC_Range.t): (FPAU.error_message, FPA.decl list) either =
  match String.split_on_char ':' contents with
  | [id_str; expr_str] ->
    let id = mk_ident id_str r in
    let tm = match int_of_string_opt expr_str with
      | Some int_lit -> FPA.mk_term (FPA.Const (FStarC_Const.Const_int (string_of_int int_lit, None))) r FPA.Expr
      | None -> FPA.mk_term (FPA.Var (mk_lident expr_str r)) r FPA.Expr
    in
    let q = FPA.NoLetQualifier in
    let pat = FPA.mk_pattern (FPA.PatVar (id, None, [])) r in
    let let_decl = FPA.mk_decl (FPA.TopLevelLet (q, [pat, tm])) r [] in
    Inr [let_decl]
  | _ -> err "bad let" r

let parse_line (contents: string) (r: FStarC_Range.t): (FPAU.error_message, FPA.decl list) either =
  match take_prefix "module:" contents with
  | Some mod_name ->
      let lid = mk_lident mod_name r in
      Inr [FPA.mk_decl (FPA.TopLevelModule lid) r []]
  | None ->
    match take_prefix "let:" contents with
    | Some rest ->
      parse_let rest r
    | None ->
      match take_prefix "comment:" contents with
      | Some _ -> Inr []
      | None ->
        if contents = "" then Inr []
        else err "bad decl" r

let parse_tiny_decls (contents: string) (r: FStarC_Range.t): (FPAU.error_message, FPA.decl list) either =
  let rec go acc ls =
    match ls with
    | [] -> Inr acc
    | l::ls ->
      match parse_line l r with
      | Inl err -> Inl err
      | Inr decls -> go (acc @ decls) ls
  in
  let lines = String.split_on_char '\n' contents in
  go [] lines

let parse_tiny: FPAU.extension_lang_parser = { parse_decls = parse_tiny_decls }

let () = FStarC_Parser_AST_Util.register_extension_lang_parser "tiny" parse_tiny;
