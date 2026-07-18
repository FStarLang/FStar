open Prims
type 'a monoid = {
  mzero: 'a ;
  mplus: 'a -> 'a -> 'a }
let __proj__Mkmonoid__item__mzero (projectee : 'a monoid) : 'a=
  match projectee with | { mzero; mplus;_} -> mzero
let __proj__Mkmonoid__item__mplus (projectee : 'a monoid) : 'a -> 'a -> 'a=
  match projectee with | { mzero; mplus;_} -> mplus
let mzero (projectee : 'a monoid) : 'a=
  match projectee with | { mzero = mzero1; mplus;_} -> mzero1
let mplus (projectee : 'a monoid) : 'a -> 'a -> 'a=
  match projectee with | { mzero = mzero1; mplus = mplus1;_} -> mplus1
let op_Plus_Plus (uu___ : 'a monoid) : 'a -> 'a -> 'a= mplus uu___
let msum (uu___ : 'a monoid) (xs : 'a Prims.list) : 'a=
  FStarC_List.fold_left (mplus uu___) (mzero uu___) xs
let monoid_int : Prims.int monoid=
  { mzero = Prims.int_zero; mplus = (fun x y -> x + y) }
let monoid_string : Prims.string monoid=
  { mzero = ""; mplus = (fun x y -> Prims.strcat x y) }
let monoid_list (uu___ : unit) : 'a Prims.list monoid=
  { mzero = []; mplus = (fun x y -> FStarC_List.op_At x y) }
