open Prims
exception NotAListLiteral 
let (uu___is_NotAListLiteral : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotAListLiteral -> true | uu____5 -> false
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | TacticFailure uu____15 -> true | uu____16 -> false
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | TacticFailure uu____22 -> uu____22
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | EExn uu____32 -> true | uu____33 -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu____39 -> uu____39