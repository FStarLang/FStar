#light "off"
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
        Pars.init() |> ignore;
        Norm.run_all ();
        if Unif.run_all () then () else exit 1;
        exit 0
    with Error(err, msg, r) when not <| FStar.Options.trace_error() ->
         if r = FStar.Range.dummyRange
         then BU.print_string msg
         else BU.print2 "%s: %s\n" (FStar.Range.string_of_range r) msg;
         exit 1
