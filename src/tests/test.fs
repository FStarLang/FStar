#light "off"
module FStar.Tests.Test
open FStar.Syntax
open FStar
open FStar.Errors
open Expecto
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
let r = Range.dummyRange
[<EntryPoint>]
let main argv =
    printfn "Initializing ...";
    try
        (*Pars.init() |> ignore;
        Norm.run_all ();
        Unif.run_all ();*)
        Tc.main argv |> ignore;
        0
    with Error(msg, r) when not <| Options.trace_error()->
         if r = Range.dummyRange
         then print_string msg
         else printfn "%s: %s" (Range.string_of_range r) msg;
         -1
