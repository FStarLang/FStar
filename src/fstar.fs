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

let process_args () = 
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

let cleanup () = 
    ToSMT.Z3.cleanup();
    Util.kill_all ()

let go _ =    
  let finished (mods:list<Syntax.modul>) = 
    if !Options.silent then () else
      let msg = 
        if !Options.verify then "Verified" 
        else if !Options.pretype then "Lax type-checked"
        else "Parsed and desugared" in
      mods |> List.iter (fun m -> Util.print_string (Util.format2 "%s module: %s\n" msg (Syntax.text_of_lid m.name))) in
  let (res, filenames) = process_args () in
  match res with
    | Help ->
      Options.display_usage (Options.specs())
    | Die msg ->
      Util.print_string msg
    | GoOn ->
        if not (Option.isNone !Options.codegen) then
            Options.pretype := true;
        let fmods = Parser.Driver.parse_files (Options.prims()::filenames) in
        let solver = if !Options.verify then ToSMT.Encode.solver else ToSMT.Encode.dummy in
        let fmods = if !Options.pretype then Tc.Tc.check_modules solver fmods else fmods in
        if !Options.codegen = Some "OCaml" then begin
            try
                let mllib = Backends.OCaml.ASTTrans.mlmod_of_fstars (List.tail fmods) in
                let doc   = Backends.OCaml.Code.doc_of_mllib mllib in
                Util.print_string (FSharp.Format.pretty 120 doc)
            with Backends.OCaml.ASTTrans.OCamlFailure (rg, error) -> begin
                (* FIXME: register exception and remove this block  *)
                Util.print_string (* stderr *) <|
                Util.format2 "OCaml Backend Error: %s %s"
                    (Range.string_of_range rg)
                    (Backends.OCaml.ASTTrans.string_of_error error);
                exit 1
            end
        end;
        if !Options.codegen = Some "JavaScript" then begin
            let js = Backends.JS.Translate.js_of_fstars (List.tail fmods) in
            let doc = Backends.JS.Print.pretty_print js in
            Util.print_string (FSharp.Format.pretty 120 doc)
        end;
        finished fmods;
        let errs = Tc.Util.get_err_count () in
        if !Options.verify then begin
          if errs>0 then begin
            fprint1 ("Error: %s verification conditions could not be " ^
                     "discharged (see above)\n") (string_of_int errs);
            exit 1
            end
          else if not !Options.silent then
            print_string "All verification conditions discharged successfully\n"
        end
let () =
    try 
      go ();
      cleanup ();
      exit 0
    with 
    | e -> 
        if Util.handleable e then Util.handle_err false () e;
        if !Options.trace_error then Util.fprint2 "%s\n%s\n" e.Message e.StackTrace;
        if not (Util.handleable e || !Options.trace_error)
        then Util.print_string "Unexpected error; use the --trace_error option for more details\n";
        cleanup ();
        exit 1
