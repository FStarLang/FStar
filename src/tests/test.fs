#light "off"
module FStar.Tests.Test
open FSharp.Compatibility.OCaml
open FStar.Syntax
open FStar
open FStar.Errors
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
let r = Range.dummyRange
[<EntryPoint>]
let main argv =
    printfn "Initializing ...";
    try
        Pars.init() |> ignore;
        FStar.Tests.Tactics.test();
        Norm.run_all ();
        Unif.run_all ();
        0
    with Error(msg, r) when not <| Options.trace_error()->
         if r = Range.dummyRange
         then print_string msg
         else printfn "%s: %s" (Range.string_of_range r) msg;
         -1
