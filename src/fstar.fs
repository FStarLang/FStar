(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module Microsoft.FStar.FStar
open Microsoft.FStar
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Util
open Microsoft.FStar.Getopt
open Microsoft.FStar.Tc.Util
open Microsoft.FStar.Tc.Env

let process_args () = 
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

let cleanup () = Util.kill_all ()

let has_prims_cache (l: list<string>) :bool = List.mem "Prims.cache" l

let tc_prims () = 
    let solver = if !Options.verify then ToSMT.Encode.solver else ToSMT.Encode.dummy in
    let env = Tc.Env.initial_env solver Const.prims_lid in
    env.solver.init env; 
    
    let p = Options.prims () in
    let dsenv, prims_mod = Parser.Driver.parse (Parser.DesugarEnv.empty_env()) (Inl p) in
    let prims_mod, env = Tc.Tc.check_module env (List.hd prims_mod) in
    prims_mod, dsenv, env

let report_errors nopt = 
    let errs = match nopt with
        | None -> Tc.Errors.get_err_count ()
        | Some n -> n in
    if errs>0 
    then begin
        fprint1 "Error: %s errors were reported (see above)\n" (string_of_int errs);
        exit 1
    end

let tc_one_file dsenv env fn = 
    let dsenv, fmods = Parser.Driver.parse dsenv fn in
    let env, all_mods = fmods |> List.fold_left (fun (env, all_mods) m -> 
        let ms, env = Tc.Tc.check_module env m in
        env, ms) (env, []) in
    dsenv, env, List.rev all_mods

type input_chunks = 
    | Push
    | Pop
    | Code of string * (string * string)
    
let interactive_mode () = 
    if Option.isSome !Options.codegen
    then (Util.print_string "Code-generation is not supported in interactive mode"; exit 1);

    let prims_mod, dsenv, env = tc_prims () in

    let chunk = Util.new_string_builder () in
    let stdin = Util.open_stdin () in
    let rec fill_chunk ()= 
        let line = match Util.read_line stdin with 
            | None -> exit 0
            | Some l -> l in
//        Printf.printf "Read line <%s>\n" line;
        let l = Util.trim_string line in 
        if Util.starts_with l "#end"
        then begin
            let responses = match Util.split l " " with 
                | [_; ok; fail] -> (ok, fail)
                | _ -> ("ok", "fail") in
            let str = Util.string_of_string_builder chunk in 
            Util.clear_string_builder chunk; Code (str, responses)
        end
        else if l = "#pop"
        then (Util.clear_string_builder chunk; Pop)
        else if l = "#push"
        then (Util.clear_string_builder chunk; Push)
        else if l = "#finish"
        then exit 0
        else (Util.string_builder_append chunk line;
              Util.string_builder_append chunk "\n";
              fill_chunk()) in

    let rec go dsenv env = 
        match fill_chunk () with 
            | Pop -> 
              let dsenv = Parser.DesugarEnv.pop dsenv in
              let env = Tc.Env.pop env in
              env.solver.refresh();
              Options.reset_options() |> ignore;
              go dsenv env

            | Push -> 
              let dsenv = Parser.DesugarEnv.push dsenv in
              let env = Tc.Env.push env in
              go dsenv env
            
            | Code (text, (ok, fail)) ->
              let dsenv, env, mods = tc_one_file dsenv env (Inr text) in
              let n = Tc.Errors.report_all() in
              if n=0
              then Util.fprint1 "\n%s\n" ok
              else Util.fprint1 "\n%s\n" fail;
              go dsenv env in

    go dsenv env


let batch_mode_tc filenames = 
    let prims_mod, dsenv, env = tc_prims () in

    let all_mods, _, env = filenames |> List.fold_left (fun (all_mods, dsenv, env) f -> 
        let dsenv, env, ms = tc_one_file dsenv env (Inl f) in
        all_mods@ms, dsenv, env)
        (prims_mod, dsenv, env) in
   
    env.solver.finish();
    all_mods

let finished_message fmods =
    if not !Options.silent 
    then begin
        let msg = 
            if !Options.verify then "Verified" 
            else if !Options.pretype then "Lax type-checked"
            else "Parsed and desugared" in
         fmods |> List.iter (fun m -> Util.print_string (Util.format2 "%s module: %s\n" msg (Syntax.text_of_lid m.name)));
         print_string "All verification conditions discharged successfully\n"
    end

let codegen fmods = 
    if !Options.codegen = Some "OCaml" then begin
        try
            let mllib = Backends.OCaml.ASTTrans.mlmod_of_fstars (List.tail fmods) in
            let doc   = Backends.OCaml.Code.doc_of_mllib mllib in
            List.iter (fun (n,d) -> Util.write_file (Options.prependOutputDir (n^".ml")) (FSharp.Format.pretty 120 d)) doc
        with Backends.OCaml.ASTTrans.OCamlFailure (rg, error) -> begin
            (* FIXME: register exception and remove this block  *)
            Util.print_string (* stderr *) <|
            Util.format2 "OCaml Backend Error: %s %s\n"
                (Range.string_of_range rg)
                (Backends.OCaml.ASTTrans.string_of_error error);
            exit 1
        end
    end
//    ;
//    if !Options.codegen = Some "JavaScript" then begin
//        let js = Backends.JS.Translate.js_of_fstars (List.tail fmods) in
//        let doc = Backends.JS.Print.pretty_print js in
//        Util.print_string (FSharp.Format.pretty 120 doc)
//    end
//    
(* Main function *)
let go _ =    
  let (res, filenames) = process_args () in
  match res with
    | Help ->
      Options.display_usage (Options.specs())
    | Die msg ->
      Util.print_string msg
    | GoOn ->
        if !Options.interactive 
        then interactive_mode () 
        else let filenames = if !Options.use_build_config  //if the user explicitly requested it
                             //|| Sys.argv.Length = 2        //or, if there is only a single file on the command line
                             then match filenames with 
                                    | [f] -> Parser.Driver.read_build_config f //then, try to read a build config from the header of the file
                                    | _ -> Util.print_string "--use_build_config expects just a single file on the command line and no other arguments"; exit 1
                             else filenames in
             
             let fmods = batch_mode_tc filenames  in
             report_errors None;
             codegen fmods;
             finished_message fmods


let main () =
    try 
      go ();
      cleanup ();
      exit 0
    with 
    | e -> 
        if Util.handleable e then Util.handle_err false () e;
        if !Options.trace_error
        then Util.fprint2 "\nUnexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
        else if not (Util.handleable e)
        then Util.fprint1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e);
        cleanup ();
        exit 1
