#light "off"
module FStar.Tests.Test
open FStar.Compiler.Effect
open FStar.Syntax
open FStar.Errors
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
module BU = FStar.Compiler.Util

let main argv =
    BU.print_string "Initializing ...\n";
    try
        FStar.Main.setup_hooks();
        Pars.init() |> ignore;
        Norm.run_all ();
        if Unif.run_all () then () else exit 1;
        exit 0
    with Error(err, msg, r, _ctx) when not <| FStar.Options.trace_error() ->
         if r = FStar.Compiler.Range.dummyRange
         then BU.print_string msg
         else BU.print2 "%s: %s\n" (FStar.Compiler.Range.string_of_range r) msg;
         exit 1
