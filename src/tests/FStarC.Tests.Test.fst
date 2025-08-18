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
module FStarC.Tests.Test
open FStarC
open FStarC.Effect
open FStarC.Syntax
open FStarC.Errors
module BU = FStarC.Util
module O = FStarC.Options
module G = FStarC.Getopt
open FStarC.Format
open FStarC.Class.Show

open FStarC.Hooks (* KEEP: we need this module for its top-level effect. *)

let handle_error e =
    if FStarC.Errors.handleable e then
      FStarC.Errors.err_exn e
    else begin
      Format.print1_error "Unexpected error: %s\n" (BU.message_of_exn e);
      if Options.trace_error() then
        print1_error "Trace:\n%s\n" (BU.trace_of_exn e)
      else
        print_error "Please file a bug report, ideally with a minimized version of the source program that triggered the error.\n"
    end;
    FStarC.Errors.report_all () |> ignore;
    ()

let main () =
    Format.print_string "Initializing tests...\n";
    try
        let res, fs = O.parse_cmd_line () in
        match res with
        | G.Error (msg, _) ->
          Format.print_error msg; exit 1
        | G.Empty
        | G.Success ->
          ignore (Options.set_options "--error_contexts true");
          if Debug.any () then (
            print3 "- F* version %s -- %s (on %s)\n"  !Options._version !Options._commit (Platform.kernel ());
            print1 "- Executable: %s\n" (BU.exec_name);
            print1 "- Library root: %s\n" (Option.dflt "<none>" (Find.lib_root ()));
            print1 "- Full include path: %s\n" (show (Find.full_include_path ()));
            print_string "\n";
            ()
          );
          Pars.do_init ();
          Pars.parse_incremental_decls();
          Pars.parse_incremental_decls_use_lang ();
          Norm.run_all ();
          if Unif.run_all () then () else exit 1;
          Data.run_all ();

          FStarC.Errors.report_all () |> ignore;
          let nerrs = FStarC.Errors.get_err_count() in
          if nerrs > 0 then (
            ignore (Errors.report_all ());
            exit 1
          );
          exit 0
    with
    | e ->
      handle_error e;
      exit 1
