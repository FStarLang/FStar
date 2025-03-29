open Fstarcompiler
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
let (uu___is_Simpl : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Simpl -> true
    | uu___ -> false
let (uu___is_Weak : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Weak -> true
    | uu___ -> false
let (uu___is_HNF : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.HNF -> true
    | uu___ -> false
let (uu___is_Primops :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Primops -> true
    | uu___ -> false
let (uu___is_Delta : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Delta -> true
    | uu___ -> false
let (uu___is_Zeta : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Zeta -> true
    | uu___ -> false
let (uu___is_ZetaFull :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.ZetaFull -> true
    | uu___ -> false
let (uu___is_Iota : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Iota -> true
    | uu___ -> false
let (uu___is_NBE : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.NBE -> true
    | uu___ -> false
let (uu___is_Reify : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Reify -> true
    | uu___ -> false
let (uu___is_NormDebug :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.NormDebug -> true
    | uu___ -> false
let (uu___is_UnfoldOnly :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldOnly _0 -> true
    | uu___ -> false
let (__proj__UnfoldOnly__item___0 :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | Fstarcompiler.FStarC_NormSteps.UnfoldOnly _0 -> _0
let (uu___is_UnfoldOnce :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldOnce _0 -> true
    | uu___ -> false
let (__proj__UnfoldOnce__item___0 :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | Fstarcompiler.FStarC_NormSteps.UnfoldOnce _0 -> _0
let (uu___is_UnfoldFully :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldFully _0 -> true
    | uu___ -> false
let (__proj__UnfoldFully__item___0 :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldAttr _0 -> true
    | uu___ -> false
let (__proj__UnfoldAttr__item___0 :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | Fstarcompiler.FStarC_NormSteps.UnfoldAttr _0 -> _0
let (uu___is_UnfoldQual :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldQual _0 -> true
    | uu___ -> false
let (__proj__UnfoldQual__item___0 :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | Fstarcompiler.FStarC_NormSteps.UnfoldQual _0 -> _0
let (uu___is_UnfoldNamespace :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldNamespace _0 -> true
    | uu___ -> false
let (__proj__UnfoldNamespace__item___0 :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.UnfoldNamespace _0 -> _0
let (uu___is_Unmeta : Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Unmeta -> true
    | uu___ -> false
let (uu___is_Unascribe :
  Fstarcompiler.FStarC_NormSteps.norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fstarcompiler.FStarC_NormSteps.Unascribe -> true
    | uu___ -> false
let (simplify : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Simpl
let (weak : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Weak
let (hnf : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.HNF
let (primops : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Primops
let (delta : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Delta
let (norm_debug : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.NormDebug
let (zeta : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Zeta
let (zeta_full : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.ZetaFull
let (iota : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Iota
let (nbe : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.NBE
let (reify_ : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Reify
let (delta_only :
  Prims.string Prims.list -> Fstarcompiler.FStarC_NormSteps.norm_step) =
  fun s -> Fstarcompiler.FStarC_NormSteps.UnfoldOnly s
let (delta_once :
  Prims.string Prims.list -> Fstarcompiler.FStarC_NormSteps.norm_step) =
  fun s -> Fstarcompiler.FStarC_NormSteps.UnfoldOnce s
let (delta_fully :
  Prims.string Prims.list -> Fstarcompiler.FStarC_NormSteps.norm_step) =
  fun s -> Fstarcompiler.FStarC_NormSteps.UnfoldFully s
let (delta_attr :
  Prims.string Prims.list -> Fstarcompiler.FStarC_NormSteps.norm_step) =
  fun s -> Fstarcompiler.FStarC_NormSteps.UnfoldAttr s
let (delta_qualifier :
  Prims.string Prims.list -> Fstarcompiler.FStarC_NormSteps.norm_step) =
  fun s -> Fstarcompiler.FStarC_NormSteps.UnfoldQual s
let (delta_namespace :
  Prims.string Prims.list -> Fstarcompiler.FStarC_NormSteps.norm_step) =
  fun s -> Fstarcompiler.FStarC_NormSteps.UnfoldNamespace s
let (unmeta : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Unmeta
let (unascribe : Fstarcompiler.FStarC_NormSteps.norm_step) =
  Fstarcompiler.FStarC_NormSteps.Unascribe
