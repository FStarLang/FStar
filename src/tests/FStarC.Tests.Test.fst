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
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module BU = FStarC.Util
module O = FStarC.Options
module G = FStarC.Getopt

let main argv =
    BU.print_string "Initializing tests...\n";
    try
        let res, fs = O.parse_cmd_line () in
        match res with
        | G.Help ->
          BU.print_string "F* unit tests. This binary can take the same options \
                           as F*, but not all of them are meaningful.";
          exit 0
        | G.Error (msg, _) ->
          BU.print_error msg; exit 1
        | G.Empty
        | G.Success ->
          FStarC.Hooks.setup_hooks();
          Pars.init() |> ignore;
          Pars.parse_incremental_decls();
          Pars.parse_incremental_decls_use_lang ();
          Norm.run_all ();
          if Unif.run_all () then () else exit 1;
          Data.run_all ();

          FStarC.Errors.report_all () |> ignore;
          let nerrs = FStarC.Errors.get_err_count() in
          if nerrs > 0 then
            exit 1;
          exit 0
    with 
      | Error(err, msg, r, _ctx) when not <| O.trace_error() ->
        if r = FStarC.Range.dummyRange
        then BU.print_string (Errors.rendermsg msg)
        else BU.print2 "%s: %s\n" (FStarC.Range.string_of_range r) (Errors.rendermsg msg);
        exit 1
      | e ->
        BU.print2_error "Error\n%s\n%s\n" (BU.message_of_exn e) (BU.trace_of_exn e);
        exit 1
