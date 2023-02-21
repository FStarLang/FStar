open Prims
exception NotAListLiteral 
let (uu___is_NotAListLiteral : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotAListLiteral -> true | uu___ -> false
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | TacticFailure uu___ -> true | uu___ -> false
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | TacticFailure uu___ -> uu___
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | EExn uu___ -> true | uu___ -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu___ -> uu___