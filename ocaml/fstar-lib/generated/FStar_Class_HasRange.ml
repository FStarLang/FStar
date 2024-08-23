open Prims
type 'a hasRange =
  {
  pos: 'a -> FStar_Compiler_Range_Type.range ;
  setPos: FStar_Compiler_Range_Type.range -> 'a -> 'a }
let __proj__MkhasRange__item__pos :
  'a . 'a hasRange -> 'a -> FStar_Compiler_Range_Type.range =
  fun x4 -> match x4 with | { pos = apos; setPos = asetPos;_} -> apos
let pos : 'a . 'a hasRange -> 'a -> FStar_Compiler_Range_Type.range =
  fun x4 -> __proj__MkhasRange__item__pos x4
let __proj__MkhasRange__item__setPos :
  'a . 'a hasRange -> FStar_Compiler_Range_Type.range -> 'a -> 'a =
  fun x5 -> match x5 with | { pos = apos; setPos = asetPos;_} -> asetPos
let setPos : 'a . 'a hasRange -> FStar_Compiler_Range_Type.range -> 'a -> 'a
  = fun x5 -> __proj__MkhasRange__item__setPos x5