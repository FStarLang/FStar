#load "FStarCustard.fs"
#load "Native_runtime.fs"

let (_ : bigint) = Native_runtime.example_Effects_NativeRuntime_early true
if not (Native_runtime.example_Effects_NativeRuntime_test ()) then
    failwith "native Pulse exception regression"
let trace = ResizeArray<uint32>()
if not (Native_runtime.example_Effects_NativeRuntime_stress trace.Add) then
    failwith "native Pulse exception stress regression"
let expected =
    [100u; 2u; 1u; 101u; 2u; 1u; 102u; 2u; 1u; 200u; 3u; 5u; 4u; 5u; 201u; 8u; 7u; 300u]
    @ [0u .. 256u] @ [400u] @ List.replicate 1000 6u
if List.ofSeq trace <> expected then
    failwith "native Pulse cleanup order/count regression"
printfn "native exceptions: all execution checks passed"
