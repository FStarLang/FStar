(*
   Copyright 2008-2018 Microsoft Research

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
﻿#light "off"
module FStar.Tests.Test
open FStar.All
open FStar.Syntax
open FStar.Errors
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
module BU = FStar.Util

[<EntryPoint>] // JUST FSHARP
let main argv =
    BU.print_string "Initializing ...\n";
    try
        FStar.Main.setup_hooks();
        Pars.init() |> ignore;
        Norm.run_all ();
        if Unif.run_all () then () else exit 1;
        exit 0
    with Error(err, msg, r) when not <| FStar.Options.trace_error() ->
         if r = FStar.Range.dummyRange
         then BU.print_string msg
         else BU.print2 "%s: %s\n" (FStar.Range.string_of_range r) msg;
         exit 1
