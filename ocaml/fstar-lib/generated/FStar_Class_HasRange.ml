open Prims
type 'a hasRange =
  {
  pos: 'a -> FStar_Compiler_Range_Type.range ;
  setPos: FStar_Compiler_Range_Type.range -> 'a -> 'a }
let __proj__MkhasRange__item__pos :
  'a . 'a hasRange -> 'a -> FStar_Compiler_Range_Type.range =
  fun projectee -> match projectee with | { pos; setPos;_} -> pos
let __proj__MkhasRange__item__setPos :
  'a . 'a hasRange -> FStar_Compiler_Range_Type.range -> 'a -> 'a =
  fun projectee -> match projectee with | { pos; setPos;_} -> setPos
let pos : 'a . 'a hasRange -> 'a -> FStar_Compiler_Range_Type.range =
  fun projectee -> match projectee with | { pos = pos1; setPos;_} -> pos1
let setPos : 'a . 'a hasRange -> FStar_Compiler_Range_Type.range -> 'a -> 'a
  =
  fun projectee ->
    match projectee with | { pos = pos1; setPos = setPos1;_} -> setPos1
let (hasRange_range : FStar_Compiler_Range_Type.range hasRange) =
  { pos = (fun x -> x); setPos = (fun r -> fun uu___ -> r) }