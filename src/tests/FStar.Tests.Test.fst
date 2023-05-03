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
module FStar.Tests.Test
open FStar.Compiler.Effect
open FStar.Syntax
open FStar.Errors
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
module BU = FStar.Compiler.Util
module O = FStar.Options
module G = FStar.Getopt

let main argv =
    BU.print_string "Initializing tests...\n";
    try
        let res, fs = O.parse_cmd_line () in
        match res with
        | G.Help ->
          BU.print_string "F* unit tests. This binary can take the same options \
                           as F*, but not all of them are meaningful.";
          exit 0
        | G.Error msg ->
          BU.print_error msg; exit 1
        | G.Empty
        | G.Success ->
          FStar.Main.setup_hooks();
          Pars.init() |> ignore;
          Pars.parse_incremental_decls();
          Norm.run_all ();
          if Unif.run_all () then () else exit 1;
          exit 0
    with 
      | Error(err, msg, r, _ctx) when not <| O.trace_error() ->
        if r = FStar.Compiler.Range.dummyRange
        then BU.print_string msg
        else BU.print2 "%s: %s\n" (FStar.Compiler.Range.string_of_range r) msg;
        exit 1
      | Err (raw_error, s, ls) when not <| O.trace_error() ->
        BU.print2 "%s : [%s]\n" s (String.concat "; " ls);
        exit 1
      | e ->
        BU.print2_error "Error\n%s\n%s\n" (BU.message_of_exn e) (BU.trace_of_exn e);
        exit 1
