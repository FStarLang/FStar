open Prims
type 'a additive = {
  zero: 'a ;
  plus: 'a -> 'a -> 'a }
let __proj__Mkadditive__item__zero : 'a . 'a additive -> 'a =
  fun projectee -> match projectee with | { zero; plus;_} -> zero
let __proj__Mkadditive__item__plus : 'a . 'a additive -> 'a -> 'a -> 'a =
  fun projectee -> match projectee with | { zero; plus;_} -> plus
let zero : 'a . 'a additive -> 'a =
  fun projectee -> match projectee with | { zero = zero1; plus;_} -> zero1
let plus : 'a . 'a additive -> 'a -> 'a -> 'a =
  fun projectee ->
    match projectee with | { zero = zero1; plus = plus1;_} -> plus1
let op_Plus_Plus : 'a . 'a additive -> 'a -> 'a -> 'a = plus
let (add_int : Prims.int additive) = { zero = Prims.int_zero; plus = (+) }
let (add_bool : Prims.bool additive) = { zero = false; plus = (||) }
let add_list : 'a . unit -> 'a Prims.list additive =
  fun uu___ -> { zero = []; plus = FStar_List_Tot_Base.append }