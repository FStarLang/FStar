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
open Microsoft.FStar.Backends

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
    let dsenv, prims_mod = Parser.Driver.parse_file (Parser.DesugarEnv.empty_env()) p in
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
    let dsenv, fmods = Parser.Driver.parse_file dsenv fn in
    let env, all_mods = fmods |> List.fold_left (fun (env, all_mods) m -> 
        let ms, env = Tc.Tc.check_module env m in
        env, ms) (env, []) in
    dsenv, env, List.rev all_mods

let tc_one_fragment curmod dsenv env frag = 
    try
        match Parser.Driver.parse_fragment curmod dsenv frag with 
            | Inl (dsenv, modul) -> 
              let env = match curmod with
                | None -> env 
                | Some _ ->
                  raise (Absyn.Syntax.Err("Interactive mode only supports a single module at the top-level")) in
              let modul, npds, env = Tc.Tc.tc_partial_modul env modul in
              Some (Some (modul, npds), dsenv, env)

            | Inr (dsenv, decls) -> 
              begin match curmod with 
                | None -> failwith "Fragment without an enclosing module"
                | Some (modul,npds) -> 
                  let modul, npds', env  = Tc.Tc.tc_more_partial_modul env modul decls in
                  Some (Some (modul, npds@npds'), dsenv, env)
              end
    with 
        | Absyn.Syntax.Error(msg, r) -> 
          Tc.Errors.add_errors env [(msg,r)];
          None

        | Absyn.Syntax.Err msg -> 
          Tc.Errors.add_errors env [(msg,Absyn.Syntax.dummyRange)];
          None
        
        | e -> raise e

type input_chunks = 
    | Push of string
    | Pop  of string
    | Code of string * (string * string)
    
type stack_elt = 
    (option<(modul * list<sigelt>)>
     * Parser.DesugarEnv.env 
     * Tc.Env.env)
type stack = list<stack_elt>

let interactive_mode dsenv env = 
    let should_log = !Options.debug <> [] in
    let log = 
        if should_log 
        then let transcript = Util.open_file_for_writing "transcript" in
             (fun line -> Util.append_to_file transcript line;
                          Util.flush_file transcript)
        else (fun line -> ()) in
    if Option.isSome !Options.codegen
    then (Util.print_string "Code-generation is not supported in interactive mode"; exit 1);
    let chunk = Util.new_string_builder () in
    let stdin = Util.open_stdin () in
    let rec fill_chunk ()= 
        let line = match Util.read_line stdin with 
            | None -> exit 0
            | Some l -> l in
        log line; 
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
        else if Util.starts_with l "#pop"
        then (Util.clear_string_builder chunk; Pop l)
        else if Util.starts_with l "#push"
        then (Util.clear_string_builder chunk; Push l)
        else if l = "#finish"
        then exit 0
        else (Util.string_builder_append chunk line;
              Util.string_builder_append chunk "\n";
              fill_chunk()) in

    
    let rec go (stack:stack) curmod dsenv env = 
        begin match fill_chunk () with 
            | Pop msg -> 
              Tc.Env.pop env msg |> ignore;
              env.solver.refresh();
              Options.reset_options() |> ignore;
              let (curmod, dsenv, env), stack = match stack with 
                | [] -> failwith "Too many pops"
                | hd::tl -> hd, tl in
              go stack curmod dsenv env

            | Push msg -> 
              let stack = (curmod, dsenv, env)::stack in
              let dsenv = Parser.DesugarEnv.push dsenv in
              let env = Tc.Env.push env msg in
              go stack curmod dsenv env
            
            | Code (text, (ok, fail)) ->
                let mark dsenv env = 
                    let dsenv = Parser.DesugarEnv.mark dsenv in
                    let env = Tc.Env.mark env in
                    dsenv, env in 

                let reset_mark dsenv env = 
                    let dsenv = Parser.DesugarEnv.reset_mark dsenv in
                    let env = Tc.Env.reset_mark env in
                    dsenv, env in 

                let commit_mark dsenv env = 
                    let dsenv = Parser.DesugarEnv.commit_mark dsenv in
                    let env = Tc.Env.commit_mark env in
                    dsenv, env in 

              let fail curmod dsenv_mark env_mark =
                Tc.Errors.report_all() |> ignore;
                Tc.Errors.num_errs := 0;
                Util.fprint1 "%s\n" fail;
                let dsenv, env = reset_mark dsenv_mark env_mark in
                go stack curmod dsenv env in

              let dsenv_mark, env_mark = mark dsenv env in 
              let res = tc_one_fragment curmod dsenv_mark env_mark text in

              begin match res with 
                | Some (curmod, dsenv, env) -> 
                  if !Tc.Errors.num_errs=0
                  then begin
                     Util.fprint1 "\n%s\n" ok;
                     let dsenv, env = commit_mark dsenv env in
                     go stack curmod dsenv env
                  end 
                  else fail curmod dsenv_mark env_mark

                | _ -> 
                  fail curmod dsenv_mark env_mark
              end
        end in

    go [] None dsenv env


let batch_mode_tc filenames = 
    let prims_mod, dsenv, env = tc_prims () in

    let all_mods, dsenv, env = filenames |> List.fold_left (fun (all_mods, dsenv, env) f -> 
        Util.reset_gensym();
        let dsenv, env, ms = tc_one_file dsenv env f in
        all_mods@ms, dsenv, env)
        (prims_mod, dsenv, env) in
   
    if !Options.interactive && Tc.Errors.get_err_count () = 0
    then env.solver.refresh()
    else env.solver.finish();
    all_mods, dsenv, env

let finished_message fmods =
    if not !Options.silent 
    then begin
        let msg = 
            if !Options.verify then "Verified" 
            else if !Options.pretype then "Lax type-checked"
            else "Parsed and desugared" in
         fmods |> List.iter (fun m -> 
            if Options.should_verify m.name.str
            then Util.print_string (Util.format2 "%s module: %s\n" msg (Syntax.text_of_lid m.name)));
         print_string "All verification conditions discharged successfully\n"
    end

let codegen fmods env= 
    if !Options.codegen = Some "OCaml" then 
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
    else if !Options.codegen = Some "OCaml-experimental" then begin
        let c, mllibs = Util.fold_map Backends.ML.ExtractMod.extract (Backends.ML.ExtractTyp.mkContext env) fmods in
        let newDocs = List.collect Backends.OCaml.Code.doc_of_mllib mllibs in
            List.iter (fun (n,d) -> Util.write_file (Options.prependOutputDir (n^".ml")) (FSharp.Format.pretty 120 d)) newDocs
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
             let filenames = if !Options.use_build_config  //if the user explicitly requested it
                             || (not !Options.interactive && List.length filenames = 1)  //or, if there is only a single file on the command line
                             then match filenames with 
                                    | [f] -> Parser.Driver.read_build_config f //then, try to read a build config from the header of the file
                                    | _ -> Util.print_string "--use_build_config expects just a single file on the command line and no other arguments"; exit 1
                             else filenames in
             
             let fmods, dsenv, env = batch_mode_tc filenames  in
             report_errors None;
             if !Options.interactive 
             then interactive_mode dsenv env
             else begin
                codegen fmods env;
                finished_message fmods
             end


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
