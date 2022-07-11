#r "../../../bin/ulibfs.dll"
#r "bin/net6.0/Debug/BinarySearch.dll"
open BinarySearch

open FStar_Seq_Base

let sequence = MkSeq ([ 5; 3; 86; 23; 11; 98; 1; ] |> List.map (Prims.of_int))
let found_98 = bsearch sequence (Prims.of_int 98)
match found_98 with
| FStar_Pervasives_Native.Some a -> printfn "Found 98"
| FStar_Pervasives_Native.None -> failwith "Didn't find 98"

let found_30 = bsearch sequence (Prims.of_int 30)
match found_30 with
| FStar_Pervasives_Native.None -> printfn "Didn't find 30"
| FStar_Pervasives_Native.Some a -> failwith "30 shouldn't exist!"


