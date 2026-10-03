module FStar_List
open Prims
//open FStar.List.Tot.Base

let hd = List.head
let tail = List.tail
let tl = List.tail

let nth l i = List.nth l (Microsoft.FSharp.Core.Operators.int i)
let map = List.map
let mapT = map
let mapi f l = List.mapi (fun i x -> f (System.Numerics.BigInteger.op_Implicit i) x) l
let map2 = List.map2
let rec map3 = List.map3
let iter = List.iter
let iteri_aux _ _ _ = failwith "FStar.List.fs: Not implemented: iteri_aux"
let iteri f l = List.iteri (fun i x -> f (System.Numerics.BigInteger.op_Implicit i) x) l
let partition = List.partition
let fold_left = List.fold
let fold_right = List.foldBack
let fold_left2 = List.fold2
let collect = List.collect
let filter = List.filter
let sortWith f l = List.sortWith (fun x y -> Microsoft.FSharp.Core.Operators.int (f x y)) l
let for_all = List.forall
let forall2 = List.forall2
let tryFind f l = List.tryFind f l
let tryPick f l = List.tryPick f l
let choose = List.choose
let zip = List.zip
let splitAt x l = List.splitAt ( Microsoft.FSharp.Core.Operators.int x) l
let filter_map = List.choose
let index f l = System.Numerics.BigInteger.op_Implicit (List.findIndex f l)
