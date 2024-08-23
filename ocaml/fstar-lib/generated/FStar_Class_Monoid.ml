open Prims
type 'a monoid = {
  mzero: 'a ;
  mplus: 'a -> 'a -> 'a }
let __proj__Mkmonoid__item__mzero : 'a . 'a monoid -> 'a =
  fun x4 -> match x4 with | { mzero = amzero; mplus = amplus;_} -> amzero
let mzero : 'a . 'a monoid -> 'a = fun x4 -> __proj__Mkmonoid__item__mzero x4
let __proj__Mkmonoid__item__mplus : 'a . 'a monoid -> 'a -> 'a -> 'a =
  fun x5 -> match x5 with | { mzero = amzero; mplus = amplus;_} -> amplus
let mplus : 'a . 'a monoid -> 'a -> 'a -> 'a =
  fun x5 -> __proj__Mkmonoid__item__mplus x5
let msum : 'a . 'a monoid -> 'a Prims.list -> 'a =
  fun uu___ ->
    fun xs -> FStar_Compiler_List.fold_left (mplus uu___) (mzero uu___) xs
let (monoid_int : Prims.int monoid) =
  { mzero = Prims.int_zero; mplus = (fun x -> fun y -> x + y) }
let (monoid_string : Prims.string monoid) =
  { mzero = ""; mplus = (fun x -> fun y -> Prims.strcat x y) }
let monoid_list : 'a . unit -> 'a Prims.list monoid =
  fun uu___ ->
    { mzero = []; mplus = (fun x -> fun y -> FStar_Compiler_List.op_At x y) }