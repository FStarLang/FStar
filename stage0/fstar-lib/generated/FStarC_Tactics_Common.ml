open Prims
exception NotAListLiteral 
let (uu___is_NotAListLiteral : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotAListLiteral -> true | uu___ -> false
exception TacticFailure of (FStarC_Errors_Msg.error_message *
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option) 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | TacticFailure uu___ -> true | uu___ -> false
let (__proj__TacticFailure__item__uu___ :
  Prims.exn ->
    (FStarC_Errors_Msg.error_message * FStarC_Compiler_Range_Type.range
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TacticFailure uu___ -> uu___
exception EExn of FStarC_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | EExn uu___ -> true | uu___ -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu___ -> uu___
exception SKIP 
let (uu___is_SKIP : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | SKIP -> true | uu___ -> false