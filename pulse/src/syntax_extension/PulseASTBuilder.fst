module PulseASTBuilder
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

let extension_parser
  : AU.extension_parser
  = fun ctx contents rng ->
      let tm t = tm t rng in
      let str s = tm (Const (Const_string (s, rng))) in
      match Pulse.Parser.parse_peek_id contents rng with
      | Inr (err, r) ->
        Inl { message = err; range = r }

      | Inl id ->
        let splicer =
          let head = tm (Var pulse_checker_tac) in
          let lid_as_term ns = str (Ident.string_of_lid ns) in
          let namespaces = 
            mkConsList rng (List.map lid_as_term ctx.open_namespaces)
          in
          let abbrevs =
            mkConsList rng (
              List.map 
                (fun (a, m) ->
                  let a = str (Ident.string_of_id a) in
                  let m = lid_as_term m in
                  mkTuple [a;m] rng)
                ctx.module_abbreviations
            )
          in
          mkApp head [(namespaces, Nothing);
                      (abbrevs, Nothing);
                      (str contents, Nothing)]
                      rng
        in
        Inr (Splice (true, [Ident.id_of_text id], splicer))

let _ = 
    register_extension_parser "pulse" extension_parser
