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

let err msg args = Util.print_string (Util.format msg args)

let go _ =    
  let finished (mods:Syntax.modul list) = 
    mods |> List.iter (fun m -> err "Parsed and desugared module: %s\n" [Syntax.text_of_lid m.name]) in
  let (res, filenames) = process_args () in
  match res with
    | Help ->
      Options.display_usage (Options.specs())
    | Die msg ->
      err msg []
    | GoOn ->
      begin
        (* let _ = startClock () in *)
        let fmods = Parser.Driver.parse_files (Options.prims()::filenames) in
        finished fmods
      end
      
let cleanup () = ()
  (* System.Console.Out.Flush(); *)
  (* System.Console.Error.Flush() *)
    
let _ = 
  try 
    go ();
    cleanup ();
    exit 0
  with 
    | Syntax.Err msg -> err "Failure: %s\n" [msg]
    | Syntax.Error(msg, r) -> err "Failure (%s): %s" [Range.string_of_range r; msg]
    | e ->
      (err "Unexpected exception :( \n" [];
       cleanup();
       exit -1)
