#load "FStarCustard.fs"
#load "Native_runtime.fs"

let (_ : bigint) = Native_runtime.example_Effects_NativeRuntime_early true
if not (Native_runtime.example_Effects_NativeRuntime_test ()) then
    failwith "native Pulse exception regression"
printfn "native exceptions: all execution checks passed"
