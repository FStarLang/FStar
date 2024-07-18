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

module PulseSyntaxExtension.ASTBuilder
open FStar.Compiler.Effect
open FStar.Parser.AST
open FStar.Parser.AST.Util
open FStar.Ident
module BU = FStar.Compiler.Util
module List = FStar.Compiler.List
module A = FStar.Parser.AST
module AU = FStar.Parser.AST.Util
module S = FStar.Syntax.Syntax
open FStar.List.Tot
open FStar.Const

let r_ = FStar.Compiler.Range.dummyRange

#push-options "--warn_error -272" //intentional top-level effect
let pulse_checker_tac = Ident.lid_of_path ["Pulse"; "Main"; "check_pulse"] r_
let pulse_checker_after_parse_tac = Ident.lid_of_path ["Pulse"; "Main"; "check_pulse_after_parse"] r_
#pop-options
let tm t r = { tm=t; range=r; level=Un}

let parse_decl_name
  : contents:string ->
    FStar.Compiler.Range.range ->
    either AU.error_message FStar.Ident.ident
  = fun contents r ->
    match Parser.parse_peek_id contents r with
    | Inl s -> Inr (Ident.id_of_text s)
    | Inr (msg, r) -> Inl {
      AU.message = msg;
      AU.range = r;
    }

let i s r = tm (Const (Const_int(BU.string_of_int s, None))) r
let str s r = tm (Const (Const_string (s, r))) r
let lid_as_term ns r = str (Ident.string_of_lid ns) r

let encode_open_namespaces_and_abbreviations
    (ctx:open_namespaces_and_abbreviations)
    (r:FStar.Compiler.Range.range)
: term & term
= let tm t = tm t r in
  let str s = str s r in
  let lid_as_term ns = lid_as_term ns r in
  let namespaces = mkConsList r (List.map lid_as_term ctx.open_namespaces) in
  let abbrevs =
      mkConsList r (
        List.map 
            (fun (a, m) ->
              let a = str (Ident.string_of_id a) in
              let m = lid_as_term m in
              mkTuple [a;m] r)
            ctx.module_abbreviations
      )
  in
  namespaces, abbrevs

let encode_range (r:FStar.Compiler.Range.range)
: term & term & term
= let open FStar.Compiler.Range in
  let line = line_of_pos (start_of_range r) in
  let col = col_of_pos (start_of_range r) in
  str (file_of_range r) r, i line r, i col r
  
let parse_decl
  : open_namespaces_and_abbreviations ->
    contents:string ->
    FStar.Compiler.Range.range ->
    either AU.error_message decl
  = fun ctx contents r ->
      let tm t = tm t r in
      let str s = str s r in
      let i s = tm (Const (Const_int(BU.string_of_int s, None))) in
      match Parser.parse_peek_id contents r with
      | Inr (err, r) ->
        Inl { message = err; range = r }

      | Inl id ->
        let splicer =
          let head = tm (Var pulse_checker_tac) in
          let lid_as_term ns = lid_as_term ns r in
          let namespaces, abbrevs = encode_open_namespaces_and_abbreviations ctx r in
          let file_name, line, col = encode_range r in
          mkApp head [(namespaces, Nothing);
                      (abbrevs, Nothing);
                      (str contents, Nothing);
                      (file_name, Nothing);
                      (line, Nothing);
                      (col, Nothing);
                      (str id, Nothing)]
                      r
        in
        let d = Splice (true, [Ident.id_of_text id], splicer) in
        let d = { d; drange = r; quals = [ Irreducible ]; attrs = [str "uninterpreted_by_smt"]; interleaved = false  } in
        Inr d

let maybe_report_error first_error decls =
  match first_error with
  | None -> Inr decls
  | Some (raw_error, msg, r) ->
    let should_fail_on_error =
      let file = FStar.Compiler.Range.file_of_range r in
      match FStar.Parser.Dep.maybe_module_name_of_file file with
      | None -> false //don't report hard errors on <input>; we'll log them as warnings below
      | Some _ ->
        match FStar.Options.ide_filename() with
        | None -> true //we're not in IDE mode, parsing failures are fatal
        | Some fn ->
          BU.print2 "Hard error?: filename=%s; ide filename=%s\n" (BU.basename file) (BU.basename fn);
          BU.basename fn <> BU.basename file  //we're in IDE mode, failures are not fatal in the current file
    in
    if should_fail_on_error
    then (
      Inl { message = FStar.Errors.Msg.rendermsg msg; range = r }
    )
    else (
      // FStar.Errors.log_issue_doc r (raw_error, msg);
      let open FStar.Errors in
      Inr <| (decls @ [Inr <| FStar.Parser.AST.(mk_decl Unparseable r [])])
    )

let parse_extension_lang (contents:string) (r:FStar.Compiler.Range.range)
: either AU.error_message (list decl)
= match Parser.parse_lang contents r with
  | Inr None ->
    Inl { message = "#lang-pulse: Parsing failed"; range = r }
  | Inr (Some (err,r)) -> 
    Inl { message = err; range = r }
  | Inl (decls, first_error) -> (
    match maybe_report_error first_error decls with
    | Inl err -> Inl err
    | Inr decls ->
      let id_and_range_of_decl (d:PulseSyntaxExtension.Sugar.decl) =
        let open PulseSyntaxExtension.Sugar in
        match d with
        | FnDefn { id; range }
        | FnDecl { id; range } -> id, range
      in
      let splice_decl
          (ctx:open_namespaces_and_abbreviations)
          (d:PulseSyntaxExtension.Sugar.decl)
      : decl
      = let id, r = id_and_range_of_decl d in  
        let id_txt = Ident.string_of_id id in
        let decl_as_term = 
          let blob = FStar.Syntax.Util.mk_lazy d S.t_bool (S.Lazy_extension "pulse_sugar_decl") (Some r) in
          let eq (t1 t2: FStar.Syntax.Syntax.term) =
             let d1 : PulseSyntaxExtension.Sugar.decl = FStar.Syntax.Util.unlazy_as_t (S.Lazy_extension "pulse_sugar_decl") t1 in
             let d2 : PulseSyntaxExtension.Sugar.decl = FStar.Syntax.Util.unlazy_as_t (S.Lazy_extension "pulse_sugar_decl") t2 in
             PulseSyntaxExtension.Sugar.eq_decl d1 d2
          in
          tm (DesugaredBlob {tag="pulse_sugar_decl"; blob; eq}) r
        in
        let splicer =
          let head = tm (Var pulse_checker_after_parse_tac) r in
          let namespaces, abbrevs = encode_open_namespaces_and_abbreviations ctx r in
          mkApp head [(namespaces, Nothing);
                      (abbrevs, Nothing);
                      (decl_as_term, Nothing);
                      (str id_txt r, Nothing)]
                      r
        in
        let d = Splice (true, [id], splicer) in
        let d = { d; drange = r; quals = [ Irreducible ]; attrs = [str "uninterpreted_by_smt" r]; interleaved = false  } in
        d
      in
      let maybe_extend_ctx ctx d =
        match d.d with
        | Open lid -> { ctx with open_namespaces = lid::ctx.open_namespaces }
        | ModuleAbbrev (i, l) -> { ctx with module_abbreviations = (i, l)::ctx.module_abbreviations }
        | _ -> ctx
      in
      let default_opens = [ FStar.Parser.Const.pervasives_lid; FStar.Parser.Const.prims_lid; FStar.Parser.Const.fstar_ns_lid ] in
      let _, decls =
        List.fold_left 
          (fun (ctx, out) d ->
            match d with
            | Inr d -> maybe_extend_ctx ctx d, d::out
            | Inl d -> ctx, splice_decl ctx d :: out)
          ({ open_namespaces = default_opens; module_abbreviations = [] }, [])
          decls
      in
     Inr <| List.rev decls
    )
  


#push-options "--warn_error -272" //intentional top-level effect
let _ = register_extension_parser "pulse" {parse_decl_name; parse_decl}
let _ = register_extension_lang_parser "pulse" {parse_decls=parse_extension_lang}
#pop-options
   
module TcEnv = FStar.TypeChecker.Env
module D = PulseSyntaxExtension.Desugar
module L = FStar.Compiler.List
module R = FStar.Compiler.Range


let sugar_decl = PulseSyntaxExtension.Sugar.decl
let desugar_pulse (env:TcEnv.env) 
                  (namespaces:list string)
                  (module_abbrevs:list (string & string))
                  (sugar:sugar_decl)
: either PulseSyntaxExtension.SyntaxWrapper.decl (option (string & R.range))
= let namespaces = L.map Ident.path_of_text namespaces in
  let module_abbrevs = L.map (fun (x, l) -> x, Ident.path_of_text l) module_abbrevs in
  let env = D.initialize_env env namespaces module_abbrevs in
  fst (D.desugar_decl env sugar 0)

  
let parse_pulse (env:TcEnv.env) 
                (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : either PulseSyntaxExtension.SyntaxWrapper.decl (option (string & R.range))
  = let range = 
      let p = R.mk_pos line col in
      R.mk_range file_name p p
    in
    match Parser.parse_decl content range with
    | Inl d -> desugar_pulse env namespaces module_abbrevs d
    | Inr e -> Inr e
    