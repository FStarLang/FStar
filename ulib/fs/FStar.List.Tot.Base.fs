module List.Tot.Base
open Prims
module OCamlList = FSharp.Compatibility.OCaml.List

let isEmpty l = List.isEmpty l
let hd = List.head
let tail = List.tail
let tl = List.tail
let length l : int = List.length l |> System.Numerics.BigInteger.op_Implicit
let nth l i = try Some (List.nth l (Microsoft.FSharp.Core.Operators.int i)) with _ -> None
let index l i = List.nth l (Microsoft.FSharp.Core.Operators.int i)
let count _ _ = failwith "FStar_List.Tot.Base.fs: Not implemented: count"
let rev_acc _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: rev_acc"
let rev = List.rev
let append = List.append
let op_Append = append
let flatten = List.concat
let map = List.map
let mapi_init _ _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: mapi_init"
let mapi f l = List.mapi (fun i x -> f (System.Numerics.BigInteger.op_Implicit i) x) l
let concatMap f l = List.collect f l
let fold_left = List.fold
let fold_right = List.foldBack
let fold_left2 = List.fold2
let mem = List.contains
//type ('a, 'b, 'c) memP = NOT IMPLEMENTED
let contains x l = List.exists (fun y -> x = y) l
let existsb f l = List.exists f l
let find f l = List.tryFind f l
let for_all = List.forall
let collect f l = List.collect f l
let tryFind = find
let tryPick f l = List.tryPick f l
let choose = List.choose
let partition = List.partition
let subset _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: subset"
let noRepeats _ = failwith "FStar.List.Tot.Base.fs: Not implemented: noRepeats"
let assoc x l = OCamlList.try_assoc x l
let split = List.unzip
let splitAt = List.splitAt
let unzip = List.unzip

let unzip3 = List.unzip3
let bool_of_compare _ _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: bool_of_compare"
let compare_of_bool _ _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: compare_of_bool"
let sortWith f l = List.sortWith (fun x y -> Microsoft.FSharp.Core.Operators.int (f x y)) l
let list_unref l = l
