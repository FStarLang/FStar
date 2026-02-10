open Prims
exception NotAListLiteral 
let uu___is_NotAListLiteral (projectee : Prims.exn) : Prims.bool=
  match projectee with | NotAListLiteral -> true | uu___ -> false
exception TacticFailure of (FStarC_Errors_Msg.error_message *
  FStarC_Range_Type.t FStar_Pervasives_Native.option) 
let uu___is_TacticFailure (projectee : Prims.exn) : Prims.bool=
  match projectee with | TacticFailure uu___ -> true | uu___ -> false
let __proj__TacticFailure__item__uu___ (projectee : Prims.exn) :
  (FStarC_Errors_Msg.error_message * FStarC_Range_Type.t
    FStar_Pervasives_Native.option)=
  match projectee with | TacticFailure uu___ -> uu___
exception EExn of FStarC_Syntax_Syntax.term 
let uu___is_EExn (projectee : Prims.exn) : Prims.bool=
  match projectee with | EExn uu___ -> true | uu___ -> false
let __proj__EExn__item__uu___ (projectee : Prims.exn) :
  FStarC_Syntax_Syntax.term= match projectee with | EExn uu___ -> uu___
exception SKIP 
let uu___is_SKIP (projectee : Prims.exn) : Prims.bool=
  match projectee with | SKIP -> true | uu___ -> false
