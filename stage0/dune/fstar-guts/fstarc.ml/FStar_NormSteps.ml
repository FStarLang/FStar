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
  | ReduceProjections 
let uu___is_Simpl (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Simpl -> true | uu___ -> false
let uu___is_Weak (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Weak -> true | uu___ -> false
let uu___is_HNF (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.HNF -> true | uu___ -> false
let uu___is_Primops (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Primops -> true | uu___ -> false
let uu___is_Delta (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Delta -> true | uu___ -> false
let uu___is_Zeta (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Zeta -> true | uu___ -> false
let uu___is_ZetaFull (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.ZetaFull -> true | uu___ -> false
let uu___is_Iota (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Iota -> true | uu___ -> false
let uu___is_NBE (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.NBE -> true | uu___ -> false
let uu___is_Reify (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Reify -> true | uu___ -> false
let uu___is_NormDebug (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.NormDebug -> true | uu___ -> false
let uu___is_UnfoldOnly (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with
  | FStarC_NormSteps.UnfoldOnly _0 -> true
  | uu___ -> false
let __proj__UnfoldOnly__item___0 (projectee : FStarC_NormSteps.norm_step) :
  Prims.string Prims.list=
  match projectee with | FStarC_NormSteps.UnfoldOnly _0 -> _0
let uu___is_UnfoldOnce (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with
  | FStarC_NormSteps.UnfoldOnce _0 -> true
  | uu___ -> false
let __proj__UnfoldOnce__item___0 (projectee : FStarC_NormSteps.norm_step) :
  Prims.string Prims.list=
  match projectee with | FStarC_NormSteps.UnfoldOnce _0 -> _0
let uu___is_UnfoldFully (projectee : FStarC_NormSteps.norm_step) :
  Prims.bool=
  match projectee with
  | FStarC_NormSteps.UnfoldFully _0 -> true
  | uu___ -> false
let __proj__UnfoldFully__item___0 (projectee : FStarC_NormSteps.norm_step) :
  Prims.string Prims.list=
  match projectee with | FStarC_NormSteps.UnfoldFully _0 -> _0
let uu___is_UnfoldAttr (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with
  | FStarC_NormSteps.UnfoldAttr _0 -> true
  | uu___ -> false
let __proj__UnfoldAttr__item___0 (projectee : FStarC_NormSteps.norm_step) :
  Prims.string Prims.list=
  match projectee with | FStarC_NormSteps.UnfoldAttr _0 -> _0
let uu___is_UnfoldQual (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with
  | FStarC_NormSteps.UnfoldQual _0 -> true
  | uu___ -> false
let __proj__UnfoldQual__item___0 (projectee : FStarC_NormSteps.norm_step) :
  Prims.string Prims.list=
  match projectee with | FStarC_NormSteps.UnfoldQual _0 -> _0
let uu___is_UnfoldNamespace (projectee : FStarC_NormSteps.norm_step) :
  Prims.bool=
  match projectee with
  | FStarC_NormSteps.UnfoldNamespace _0 -> true
  | uu___ -> false
let __proj__UnfoldNamespace__item___0
  (projectee : FStarC_NormSteps.norm_step) : Prims.string Prims.list=
  match projectee with | FStarC_NormSteps.UnfoldNamespace _0 -> _0
let uu___is_Unmeta (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Unmeta -> true | uu___ -> false
let uu___is_Unascribe (projectee : FStarC_NormSteps.norm_step) : Prims.bool=
  match projectee with | FStarC_NormSteps.Unascribe -> true | uu___ -> false
let uu___is_ReduceProjections (projectee : FStarC_NormSteps.norm_step) :
  Prims.bool=
  match projectee with
  | FStarC_NormSteps.ReduceProjections -> true
  | uu___ -> false
let simplify : FStarC_NormSteps.norm_step= FStarC_NormSteps.Simpl
let weak : FStarC_NormSteps.norm_step= FStarC_NormSteps.Weak
let hnf : FStarC_NormSteps.norm_step= FStarC_NormSteps.HNF
let primops : FStarC_NormSteps.norm_step= FStarC_NormSteps.Primops
let delta : FStarC_NormSteps.norm_step= FStarC_NormSteps.Delta
let norm_debug : FStarC_NormSteps.norm_step= FStarC_NormSteps.NormDebug
let zeta : FStarC_NormSteps.norm_step= FStarC_NormSteps.Zeta
let zeta_full : FStarC_NormSteps.norm_step= FStarC_NormSteps.ZetaFull
let iota : FStarC_NormSteps.norm_step= FStarC_NormSteps.Iota
let nbe : FStarC_NormSteps.norm_step= FStarC_NormSteps.NBE
let reify_ : FStarC_NormSteps.norm_step= FStarC_NormSteps.Reify
let delta_only (s : Prims.string Prims.list) : FStarC_NormSteps.norm_step=
  FStarC_NormSteps.UnfoldOnly s
let delta_once (s : Prims.string Prims.list) : FStarC_NormSteps.norm_step=
  FStarC_NormSteps.UnfoldOnce s
let delta_fully (s : Prims.string Prims.list) : FStarC_NormSteps.norm_step=
  FStarC_NormSteps.UnfoldFully s
let delta_attr (s : Prims.string Prims.list) : FStarC_NormSteps.norm_step=
  FStarC_NormSteps.UnfoldAttr s
let delta_qualifier (s : Prims.string Prims.list) :
  FStarC_NormSteps.norm_step= FStarC_NormSteps.UnfoldQual s
let delta_namespace (s : Prims.string Prims.list) :
  FStarC_NormSteps.norm_step= FStarC_NormSteps.UnfoldNamespace s
let unmeta : FStarC_NormSteps.norm_step= FStarC_NormSteps.Unmeta
let unascribe : FStarC_NormSteps.norm_step= FStarC_NormSteps.Unascribe
let reduce_projections : FStarC_NormSteps.norm_step=
  FStarC_NormSteps.ReduceProjections
