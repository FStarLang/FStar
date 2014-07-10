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

let process_args () = 
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

let cleanup () = ()

let go _ =    
  let finished (mods:list<Syntax.modul>) = 
    let msg = if !Options.pretype then "Parsed, desugared, and pre-typed module:" else "Parsed and desugared module:" in
    mods |> List.iter (fun m -> Util.print_string (Util.format2 "%s %s\n" msg (Syntax.text_of_lid m.name))) in
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
        let fmods = if !Options.pretype then Tc.Tc.check_modules fmods else fmods in
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
        finished fmods 

let () =
    try 
      go ();
      cleanup ();
      exit 0
    with 
    | e when (not !Options.trace_error && Util.handleable e) ->
        Util.handle_err false () e