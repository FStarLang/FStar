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
open FStar.Const

let r_ = FStar.Compiler.Range.dummyRange

let pulse_checker_tac = Ident.lid_of_path ["Pulse"; "Main"; "check_pulse"] r_
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

let parse_decl
  : open_namespaces_and_abbreviations ->
    contents:string ->
    FStar.Compiler.Range.range ->
    either AU.error_message decl
  = fun ctx contents r ->
      let tm t = tm t r in
      let str s = tm (Const (Const_string (s, r))) in
      let i s = tm (Const (Const_int(BU.string_of_int s, None))) in
      match Parser.parse_peek_id contents r with
      | Inr (err, r) ->
        Inl { message = err; range = r }

      | Inl id ->
        let splicer =
          let head = tm (Var pulse_checker_tac) in
          let lid_as_term ns = str (Ident.string_of_lid ns) in
          let namespaces = 
            mkConsList r (List.map lid_as_term ctx.open_namespaces)
          in
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
          let file_name, line, col = 
            let open FStar.Compiler.Range in
            let line = line_of_pos (start_of_range r) in
            let col = col_of_pos (start_of_range r) in
            file_of_range r, line, col
          in
          mkApp head [(namespaces, Nothing);
                      (abbrevs, Nothing);
                      (str contents, Nothing);
                      (str file_name, Nothing);
                      (i line, Nothing);
                      (i col, Nothing);
                      (str id, Nothing)]
                      r
        in
        let d = Splice (true, [Ident.id_of_text id], splicer) in
        let d = { d; drange = r; quals = [ Irreducible ]; attrs = [str "uninterpreted_by_smt"]; interleaved = false  } in
        Inr d

#push-options "--warn_error -272" //intentional top-level effect
let _ = 
    register_extension_parser "pulse" {parse_decl_name; parse_decl}
#pop-options
   
module TcEnv = FStar.TypeChecker.Env
module D = PulseSyntaxExtension.Desugar
module L = FStar.Compiler.List
module R = FStar.Compiler.Range


let parse_pulse (env:TcEnv.env) 
                (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : either PulseSyntaxExtension.SyntaxWrapper.decl (option (string & R.range))
  = let namespaces = L.map Ident.path_of_text namespaces in
    let module_abbrevs = L.map (fun (x, l) -> x, Ident.path_of_text l) module_abbrevs in
    let env = D.initialize_env env namespaces module_abbrevs in
    let range = 
      let p = R.mk_pos line col in
      R.mk_range file_name p p
    in
    match Parser.parse_decl content range with
    | Inl d -> fst (D.desugar_decl env d 0)
    | Inr e -> Inr e
    
