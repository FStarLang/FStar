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
let rev_acc l r = List.fold_left (fun x xs -> x :: xs) r l
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
