open Prims
type 'a additive = {
  zero: 'a ;
  plus: 'a -> 'a -> 'a }
let __proj__Mkadditive__item__zero (projectee : 'a additive) : 'a=
  match projectee with | { zero; plus;_} -> zero
let __proj__Mkadditive__item__plus (projectee : 'a additive) :
  'a -> 'a -> 'a= match projectee with | { zero; plus;_} -> plus
let zero (projectee : 'a additive) : 'a=
  __proj__Mkadditive__item__zero projectee
let plus (projectee : 'a additive) : 'a -> 'a -> 'a=
  __proj__Mkadditive__item__plus projectee
let op_Plus_Plus : 'a additive -> 'a -> 'a -> 'a= plus
let add_int : Prims.int additive= { zero = Prims.int_zero; plus = (+) }
let add_bool : Prims.bool additive= { zero = false; plus = (||) }
let add_list (uu___ : unit) : 'a Prims.list additive=
  { zero = []; plus = FStar_List_Tot_Base.append }
