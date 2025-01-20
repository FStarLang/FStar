open Prims
type 'a monoid = {
  mzero: 'a ;
  mplus: 'a -> 'a -> 'a }
let __proj__Mkmonoid__item__mzero : 'a . 'a monoid -> 'a =
  fun projectee -> match projectee with | { mzero; mplus;_} -> mzero
let __proj__Mkmonoid__item__mplus : 'a . 'a monoid -> 'a -> 'a -> 'a =
  fun projectee -> match projectee with | { mzero; mplus;_} -> mplus
let mzero : 'a . 'a monoid -> 'a =
  fun projectee ->
    match projectee with | { mzero = mzero1; mplus;_} -> mzero1
let mplus : 'a . 'a monoid -> 'a -> 'a -> 'a =
  fun projectee ->
    match projectee with | { mzero = mzero1; mplus = mplus1;_} -> mplus1
let op_Plus_Plus : 'a . 'a monoid -> 'a -> 'a -> 'a =
  fun uu___ -> mplus uu___
let msum : 'a . 'a monoid -> 'a Prims.list -> 'a =
  fun uu___ ->
    fun xs -> FStarC_Compiler_List.fold_left (mplus uu___) (mzero uu___) xs
let (monoid_int : Prims.int monoid) =
  { mzero = Prims.int_zero; mplus = (fun x -> fun y -> x + y) }
let (monoid_string : Prims.string monoid) =
  { mzero = ""; mplus = (fun x -> fun y -> Prims.strcat x y) }
let monoid_list : 'a . unit -> 'a Prims.list monoid =
  fun uu___ ->
    { mzero = []; mplus = (fun x -> fun y -> FStarC_Compiler_List.op_At x y)
    }