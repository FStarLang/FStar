open Prims
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | ZetaFull 
  | Iota 
  | NBE 
  | Reify 
  | NormDebug 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldOnce of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | UnfoldQual of Prims.string Prims.list 
  | UnfoldNamespace of Prims.string Prims.list 
  | Unmeta 
  | Unascribe 
let uu___is_Simpl (projectee : norm_step) : Prims.bool=
  match projectee with | Simpl -> true | uu___ -> false
let uu___is_Weak (projectee : norm_step) : Prims.bool=
  match projectee with | Weak -> true | uu___ -> false
let uu___is_HNF (projectee : norm_step) : Prims.bool=
  match projectee with | HNF -> true | uu___ -> false
let uu___is_Primops (projectee : norm_step) : Prims.bool=
  match projectee with | Primops -> true | uu___ -> false
let uu___is_Delta (projectee : norm_step) : Prims.bool=
  match projectee with | Delta -> true | uu___ -> false
let uu___is_Zeta (projectee : norm_step) : Prims.bool=
  match projectee with | Zeta -> true | uu___ -> false
let uu___is_ZetaFull (projectee : norm_step) : Prims.bool=
  match projectee with | ZetaFull -> true | uu___ -> false
let uu___is_Iota (projectee : norm_step) : Prims.bool=
  match projectee with | Iota -> true | uu___ -> false
let uu___is_NBE (projectee : norm_step) : Prims.bool=
  match projectee with | NBE -> true | uu___ -> false
let uu___is_Reify (projectee : norm_step) : Prims.bool=
  match projectee with | Reify -> true | uu___ -> false
let uu___is_NormDebug (projectee : norm_step) : Prims.bool=
  match projectee with | NormDebug -> true | uu___ -> false
let uu___is_UnfoldOnly (projectee : norm_step) : Prims.bool=
  match projectee with | UnfoldOnly _0 -> true | uu___ -> false
let __proj__UnfoldOnly__item___0 (projectee : norm_step) :
  Prims.string Prims.list= match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldOnce (projectee : norm_step) : Prims.bool=
  match projectee with | UnfoldOnce _0 -> true | uu___ -> false
let __proj__UnfoldOnce__item___0 (projectee : norm_step) :
  Prims.string Prims.list= match projectee with | UnfoldOnce _0 -> _0
let uu___is_UnfoldFully (projectee : norm_step) : Prims.bool=
  match projectee with | UnfoldFully _0 -> true | uu___ -> false
let __proj__UnfoldFully__item___0 (projectee : norm_step) :
  Prims.string Prims.list= match projectee with | UnfoldFully _0 -> _0
let uu___is_UnfoldAttr (projectee : norm_step) : Prims.bool=
  match projectee with | UnfoldAttr _0 -> true | uu___ -> false
let __proj__UnfoldAttr__item___0 (projectee : norm_step) :
  Prims.string Prims.list= match projectee with | UnfoldAttr _0 -> _0
let uu___is_UnfoldQual (projectee : norm_step) : Prims.bool=
  match projectee with | UnfoldQual _0 -> true | uu___ -> false
let __proj__UnfoldQual__item___0 (projectee : norm_step) :
  Prims.string Prims.list= match projectee with | UnfoldQual _0 -> _0
let uu___is_UnfoldNamespace (projectee : norm_step) : Prims.bool=
  match projectee with | UnfoldNamespace _0 -> true | uu___ -> false
let __proj__UnfoldNamespace__item___0 (projectee : norm_step) :
  Prims.string Prims.list= match projectee with | UnfoldNamespace _0 -> _0
let uu___is_Unmeta (projectee : norm_step) : Prims.bool=
  match projectee with | Unmeta -> true | uu___ -> false
let uu___is_Unascribe (projectee : norm_step) : Prims.bool=
  match projectee with | Unascribe -> true | uu___ -> false
let simplify : norm_step= Simpl
let weak : norm_step= Weak
let hnf : norm_step= HNF
let primops : norm_step= Primops
let delta : norm_step= Delta
let norm_debug : norm_step= NormDebug
let zeta : norm_step= Zeta
let zeta_full : norm_step= ZetaFull
let iota : norm_step= Iota
let nbe : norm_step= NBE
let reify_ : norm_step= Reify
let delta_only (s : Prims.string Prims.list) : norm_step= UnfoldOnly s
let delta_once (s : Prims.string Prims.list) : norm_step= UnfoldOnce s
let delta_fully (s : Prims.string Prims.list) : norm_step= UnfoldFully s
let delta_attr (s : Prims.string Prims.list) : norm_step= UnfoldAttr s
let delta_qualifier (s : Prims.string Prims.list) : norm_step= UnfoldQual s
let delta_namespace (s : Prims.string Prims.list) : norm_step=
  UnfoldNamespace s
let unmeta : norm_step= Unmeta
let unascribe : norm_step= Unascribe
