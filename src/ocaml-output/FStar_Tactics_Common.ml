open Prims
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | TacticFailure uu____9 -> true | uu____10 -> false
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | TacticFailure uu____16 -> uu____16
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | EExn uu____26 -> true | uu____27 -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu____33 -> uu____33