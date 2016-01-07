#light "off"
module FStar.Tests.Test

[<EntryPoint>] 
let main argv =
    let debug = argv.Length >= 1 && argv.[0] = "debug" in
    Norm.run_all debug; 
    Unif.run_all debug;
    0
     