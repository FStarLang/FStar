open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | NoDeltaSteps 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe [@@deriving show]
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
  
type steps = step Prims.list[@@deriving show]
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  weak: Prims.bool ;
  hnf: Prims.bool ;
  primops: Prims.bool ;
  eager_unfolding: Prims.bool ;
  inlining: Prims.bool ;
  no_delta_steps: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr: FStar_Syntax_Syntax.attribute FStar_Pervasives_Native.option ;
  unfold_tac: Prims.bool ;
  pure_subterms_within_computations: Prims.bool ;
  simplify: Prims.bool ;
  erase_universes: Prims.bool ;
  allow_unbound_universes: Prims.bool ;
  reify_: Prims.bool ;
  compress_uvars: Prims.bool ;
  no_full_norm: Prims.bool ;
  check_no_uvars: Prims.bool ;
  unmeta: Prims.bool ;
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__primops
  
let (__proj__Mkfsteps__item__eager_unfolding : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__eager_unfolding
  
let (__proj__Mkfsteps__item__inlining : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__inlining
  
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_delta_steps
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Syntax_Syntax.attribute FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} ->
        __fname__pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unascribe
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    eager_unfolding = false;
    inlining = false;
    no_delta_steps = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
    unfold_attr = FStar_Pervasives_Native.None;
    unfold_tac = false;
    pure_subterms_within_computations = false;
    simplify = false;
    erase_universes = false;
    allow_unbound_universes = false;
    reify_ = false;
    compress_uvars = false;
    no_full_norm = false;
    check_no_uvars = false;
    unmeta = false;
    unascribe = false
  } 
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  ->
    let add_one1 s1 fs =
      match s1 with
      | Beta  ->
          let uu___89_1071 = fs  in
          {
            beta = true;
            iota = (uu___89_1071.iota);
            zeta = (uu___89_1071.zeta);
            weak = (uu___89_1071.weak);
            hnf = (uu___89_1071.hnf);
            primops = (uu___89_1071.primops);
            eager_unfolding = (uu___89_1071.eager_unfolding);
            inlining = (uu___89_1071.inlining);
            no_delta_steps = (uu___89_1071.no_delta_steps);
            unfold_until = (uu___89_1071.unfold_until);
            unfold_only = (uu___89_1071.unfold_only);
            unfold_attr = (uu___89_1071.unfold_attr);
            unfold_tac = (uu___89_1071.unfold_tac);
            pure_subterms_within_computations =
              (uu___89_1071.pure_subterms_within_computations);
            simplify = (uu___89_1071.simplify);
            erase_universes = (uu___89_1071.erase_universes);
            allow_unbound_universes = (uu___89_1071.allow_unbound_universes);
            reify_ = (uu___89_1071.reify_);
            compress_uvars = (uu___89_1071.compress_uvars);
            no_full_norm = (uu___89_1071.no_full_norm);
            check_no_uvars = (uu___89_1071.check_no_uvars);
            unmeta = (uu___89_1071.unmeta);
            unascribe = (uu___89_1071.unascribe)
          }
      | Iota  ->
          let uu___90_1072 = fs  in
          {
            beta = (uu___90_1072.beta);
            iota = true;
            zeta = (uu___90_1072.zeta);
            weak = (uu___90_1072.weak);
            hnf = (uu___90_1072.hnf);
            primops = (uu___90_1072.primops);
            eager_unfolding = (uu___90_1072.eager_unfolding);
            inlining = (uu___90_1072.inlining);
            no_delta_steps = (uu___90_1072.no_delta_steps);
            unfold_until = (uu___90_1072.unfold_until);
            unfold_only = (uu___90_1072.unfold_only);
            unfold_attr = (uu___90_1072.unfold_attr);
            unfold_tac = (uu___90_1072.unfold_tac);
            pure_subterms_within_computations =
              (uu___90_1072.pure_subterms_within_computations);
            simplify = (uu___90_1072.simplify);
            erase_universes = (uu___90_1072.erase_universes);
            allow_unbound_universes = (uu___90_1072.allow_unbound_universes);
            reify_ = (uu___90_1072.reify_);
            compress_uvars = (uu___90_1072.compress_uvars);
            no_full_norm = (uu___90_1072.no_full_norm);
            check_no_uvars = (uu___90_1072.check_no_uvars);
            unmeta = (uu___90_1072.unmeta);
            unascribe = (uu___90_1072.unascribe)
          }
      | Zeta  ->
          let uu___91_1073 = fs  in
          {
            beta = (uu___91_1073.beta);
            iota = (uu___91_1073.iota);
            zeta = true;
            weak = (uu___91_1073.weak);
            hnf = (uu___91_1073.hnf);
            primops = (uu___91_1073.primops);
            eager_unfolding = (uu___91_1073.eager_unfolding);
            inlining = (uu___91_1073.inlining);
            no_delta_steps = (uu___91_1073.no_delta_steps);
            unfold_until = (uu___91_1073.unfold_until);
            unfold_only = (uu___91_1073.unfold_only);
            unfold_attr = (uu___91_1073.unfold_attr);
            unfold_tac = (uu___91_1073.unfold_tac);
            pure_subterms_within_computations =
              (uu___91_1073.pure_subterms_within_computations);
            simplify = (uu___91_1073.simplify);
            erase_universes = (uu___91_1073.erase_universes);
            allow_unbound_universes = (uu___91_1073.allow_unbound_universes);
            reify_ = (uu___91_1073.reify_);
            compress_uvars = (uu___91_1073.compress_uvars);
            no_full_norm = (uu___91_1073.no_full_norm);
            check_no_uvars = (uu___91_1073.check_no_uvars);
            unmeta = (uu___91_1073.unmeta);
            unascribe = (uu___91_1073.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___92_1074 = fs  in
          {
            beta = false;
            iota = (uu___92_1074.iota);
            zeta = (uu___92_1074.zeta);
            weak = (uu___92_1074.weak);
            hnf = (uu___92_1074.hnf);
            primops = (uu___92_1074.primops);
            eager_unfolding = (uu___92_1074.eager_unfolding);
            inlining = (uu___92_1074.inlining);
            no_delta_steps = (uu___92_1074.no_delta_steps);
            unfold_until = (uu___92_1074.unfold_until);
            unfold_only = (uu___92_1074.unfold_only);
            unfold_attr = (uu___92_1074.unfold_attr);
            unfold_tac = (uu___92_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___92_1074.pure_subterms_within_computations);
            simplify = (uu___92_1074.simplify);
            erase_universes = (uu___92_1074.erase_universes);
            allow_unbound_universes = (uu___92_1074.allow_unbound_universes);
            reify_ = (uu___92_1074.reify_);
            compress_uvars = (uu___92_1074.compress_uvars);
            no_full_norm = (uu___92_1074.no_full_norm);
            check_no_uvars = (uu___92_1074.check_no_uvars);
            unmeta = (uu___92_1074.unmeta);
            unascribe = (uu___92_1074.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___93_1075 = fs  in
          {
            beta = (uu___93_1075.beta);
            iota = false;
            zeta = (uu___93_1075.zeta);
            weak = (uu___93_1075.weak);
            hnf = (uu___93_1075.hnf);
            primops = (uu___93_1075.primops);
            eager_unfolding = (uu___93_1075.eager_unfolding);
            inlining = (uu___93_1075.inlining);
            no_delta_steps = (uu___93_1075.no_delta_steps);
            unfold_until = (uu___93_1075.unfold_until);
            unfold_only = (uu___93_1075.unfold_only);
            unfold_attr = (uu___93_1075.unfold_attr);
            unfold_tac = (uu___93_1075.unfold_tac);
            pure_subterms_within_computations =
              (uu___93_1075.pure_subterms_within_computations);
            simplify = (uu___93_1075.simplify);
            erase_universes = (uu___93_1075.erase_universes);
            allow_unbound_universes = (uu___93_1075.allow_unbound_universes);
            reify_ = (uu___93_1075.reify_);
            compress_uvars = (uu___93_1075.compress_uvars);
            no_full_norm = (uu___93_1075.no_full_norm);
            check_no_uvars = (uu___93_1075.check_no_uvars);
            unmeta = (uu___93_1075.unmeta);
            unascribe = (uu___93_1075.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___94_1076 = fs  in
          {
            beta = (uu___94_1076.beta);
            iota = (uu___94_1076.iota);
            zeta = false;
            weak = (uu___94_1076.weak);
            hnf = (uu___94_1076.hnf);
            primops = (uu___94_1076.primops);
            eager_unfolding = (uu___94_1076.eager_unfolding);
            inlining = (uu___94_1076.inlining);
            no_delta_steps = (uu___94_1076.no_delta_steps);
            unfold_until = (uu___94_1076.unfold_until);
            unfold_only = (uu___94_1076.unfold_only);
            unfold_attr = (uu___94_1076.unfold_attr);
            unfold_tac = (uu___94_1076.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1076.pure_subterms_within_computations);
            simplify = (uu___94_1076.simplify);
            erase_universes = (uu___94_1076.erase_universes);
            allow_unbound_universes = (uu___94_1076.allow_unbound_universes);
            reify_ = (uu___94_1076.reify_);
            compress_uvars = (uu___94_1076.compress_uvars);
            no_full_norm = (uu___94_1076.no_full_norm);
            check_no_uvars = (uu___94_1076.check_no_uvars);
            unmeta = (uu___94_1076.unmeta);
            unascribe = (uu___94_1076.unascribe)
          }
      | Exclude uu____1077 -> failwith "Bad exclude"
      | Weak  ->
          let uu___95_1078 = fs  in
          {
            beta = (uu___95_1078.beta);
            iota = (uu___95_1078.iota);
            zeta = (uu___95_1078.zeta);
            weak = true;
            hnf = (uu___95_1078.hnf);
            primops = (uu___95_1078.primops);
            eager_unfolding = (uu___95_1078.eager_unfolding);
            inlining = (uu___95_1078.inlining);
            no_delta_steps = (uu___95_1078.no_delta_steps);
            unfold_until = (uu___95_1078.unfold_until);
            unfold_only = (uu___95_1078.unfold_only);
            unfold_attr = (uu___95_1078.unfold_attr);
            unfold_tac = (uu___95_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1078.pure_subterms_within_computations);
            simplify = (uu___95_1078.simplify);
            erase_universes = (uu___95_1078.erase_universes);
            allow_unbound_universes = (uu___95_1078.allow_unbound_universes);
            reify_ = (uu___95_1078.reify_);
            compress_uvars = (uu___95_1078.compress_uvars);
            no_full_norm = (uu___95_1078.no_full_norm);
            check_no_uvars = (uu___95_1078.check_no_uvars);
            unmeta = (uu___95_1078.unmeta);
            unascribe = (uu___95_1078.unascribe)
          }
      | HNF  ->
          let uu___96_1079 = fs  in
          {
            beta = (uu___96_1079.beta);
            iota = (uu___96_1079.iota);
            zeta = (uu___96_1079.zeta);
            weak = (uu___96_1079.weak);
            hnf = true;
            primops = (uu___96_1079.primops);
            eager_unfolding = (uu___96_1079.eager_unfolding);
            inlining = (uu___96_1079.inlining);
            no_delta_steps = (uu___96_1079.no_delta_steps);
            unfold_until = (uu___96_1079.unfold_until);
            unfold_only = (uu___96_1079.unfold_only);
            unfold_attr = (uu___96_1079.unfold_attr);
            unfold_tac = (uu___96_1079.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1079.pure_subterms_within_computations);
            simplify = (uu___96_1079.simplify);
            erase_universes = (uu___96_1079.erase_universes);
            allow_unbound_universes = (uu___96_1079.allow_unbound_universes);
            reify_ = (uu___96_1079.reify_);
            compress_uvars = (uu___96_1079.compress_uvars);
            no_full_norm = (uu___96_1079.no_full_norm);
            check_no_uvars = (uu___96_1079.check_no_uvars);
            unmeta = (uu___96_1079.unmeta);
            unascribe = (uu___96_1079.unascribe)
          }
      | Primops  ->
          let uu___97_1080 = fs  in
          {
            beta = (uu___97_1080.beta);
            iota = (uu___97_1080.iota);
            zeta = (uu___97_1080.zeta);
            weak = (uu___97_1080.weak);
            hnf = (uu___97_1080.hnf);
            primops = true;
            eager_unfolding = (uu___97_1080.eager_unfolding);
            inlining = (uu___97_1080.inlining);
            no_delta_steps = (uu___97_1080.no_delta_steps);
            unfold_until = (uu___97_1080.unfold_until);
            unfold_only = (uu___97_1080.unfold_only);
            unfold_attr = (uu___97_1080.unfold_attr);
            unfold_tac = (uu___97_1080.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1080.pure_subterms_within_computations);
            simplify = (uu___97_1080.simplify);
            erase_universes = (uu___97_1080.erase_universes);
            allow_unbound_universes = (uu___97_1080.allow_unbound_universes);
            reify_ = (uu___97_1080.reify_);
            compress_uvars = (uu___97_1080.compress_uvars);
            no_full_norm = (uu___97_1080.no_full_norm);
            check_no_uvars = (uu___97_1080.check_no_uvars);
            unmeta = (uu___97_1080.unmeta);
            unascribe = (uu___97_1080.unascribe)
          }
      | Eager_unfolding  ->
          let uu___98_1081 = fs  in
          {
            beta = (uu___98_1081.beta);
            iota = (uu___98_1081.iota);
            zeta = (uu___98_1081.zeta);
            weak = (uu___98_1081.weak);
            hnf = (uu___98_1081.hnf);
            primops = (uu___98_1081.primops);
            eager_unfolding = true;
            inlining = (uu___98_1081.inlining);
            no_delta_steps = (uu___98_1081.no_delta_steps);
            unfold_until = (uu___98_1081.unfold_until);
            unfold_only = (uu___98_1081.unfold_only);
            unfold_attr = (uu___98_1081.unfold_attr);
            unfold_tac = (uu___98_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1081.pure_subterms_within_computations);
            simplify = (uu___98_1081.simplify);
            erase_universes = (uu___98_1081.erase_universes);
            allow_unbound_universes = (uu___98_1081.allow_unbound_universes);
            reify_ = (uu___98_1081.reify_);
            compress_uvars = (uu___98_1081.compress_uvars);
            no_full_norm = (uu___98_1081.no_full_norm);
            check_no_uvars = (uu___98_1081.check_no_uvars);
            unmeta = (uu___98_1081.unmeta);
            unascribe = (uu___98_1081.unascribe)
          }
      | Inlining  ->
          let uu___99_1082 = fs  in
          {
            beta = (uu___99_1082.beta);
            iota = (uu___99_1082.iota);
            zeta = (uu___99_1082.zeta);
            weak = (uu___99_1082.weak);
            hnf = (uu___99_1082.hnf);
            primops = (uu___99_1082.primops);
            eager_unfolding = (uu___99_1082.eager_unfolding);
            inlining = true;
            no_delta_steps = (uu___99_1082.no_delta_steps);
            unfold_until = (uu___99_1082.unfold_until);
            unfold_only = (uu___99_1082.unfold_only);
            unfold_attr = (uu___99_1082.unfold_attr);
            unfold_tac = (uu___99_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1082.pure_subterms_within_computations);
            simplify = (uu___99_1082.simplify);
            erase_universes = (uu___99_1082.erase_universes);
            allow_unbound_universes = (uu___99_1082.allow_unbound_universes);
            reify_ = (uu___99_1082.reify_);
            compress_uvars = (uu___99_1082.compress_uvars);
            no_full_norm = (uu___99_1082.no_full_norm);
            check_no_uvars = (uu___99_1082.check_no_uvars);
            unmeta = (uu___99_1082.unmeta);
            unascribe = (uu___99_1082.unascribe)
          }
      | NoDeltaSteps  ->
          let uu___100_1083 = fs  in
          {
            beta = (uu___100_1083.beta);
            iota = (uu___100_1083.iota);
            zeta = (uu___100_1083.zeta);
            weak = (uu___100_1083.weak);
            hnf = (uu___100_1083.hnf);
            primops = (uu___100_1083.primops);
            eager_unfolding = (uu___100_1083.eager_unfolding);
            inlining = (uu___100_1083.inlining);
            no_delta_steps = true;
            unfold_until = (uu___100_1083.unfold_until);
            unfold_only = (uu___100_1083.unfold_only);
            unfold_attr = (uu___100_1083.unfold_attr);
            unfold_tac = (uu___100_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1083.pure_subterms_within_computations);
            simplify = (uu___100_1083.simplify);
            erase_universes = (uu___100_1083.erase_universes);
            allow_unbound_universes = (uu___100_1083.allow_unbound_universes);
            reify_ = (uu___100_1083.reify_);
            compress_uvars = (uu___100_1083.compress_uvars);
            no_full_norm = (uu___100_1083.no_full_norm);
            check_no_uvars = (uu___100_1083.check_no_uvars);
            unmeta = (uu___100_1083.unmeta);
            unascribe = (uu___100_1083.unascribe)
          }
      | UnfoldUntil d ->
          let uu___101_1085 = fs  in
          {
            beta = (uu___101_1085.beta);
            iota = (uu___101_1085.iota);
            zeta = (uu___101_1085.zeta);
            weak = (uu___101_1085.weak);
            hnf = (uu___101_1085.hnf);
            primops = (uu___101_1085.primops);
            eager_unfolding = (uu___101_1085.eager_unfolding);
            inlining = (uu___101_1085.inlining);
            no_delta_steps = (uu___101_1085.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___101_1085.unfold_only);
            unfold_attr = (uu___101_1085.unfold_attr);
            unfold_tac = (uu___101_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1085.pure_subterms_within_computations);
            simplify = (uu___101_1085.simplify);
            erase_universes = (uu___101_1085.erase_universes);
            allow_unbound_universes = (uu___101_1085.allow_unbound_universes);
            reify_ = (uu___101_1085.reify_);
            compress_uvars = (uu___101_1085.compress_uvars);
            no_full_norm = (uu___101_1085.no_full_norm);
            check_no_uvars = (uu___101_1085.check_no_uvars);
            unmeta = (uu___101_1085.unmeta);
            unascribe = (uu___101_1085.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___102_1089 = fs  in
          {
            beta = (uu___102_1089.beta);
            iota = (uu___102_1089.iota);
            zeta = (uu___102_1089.zeta);
            weak = (uu___102_1089.weak);
            hnf = (uu___102_1089.hnf);
            primops = (uu___102_1089.primops);
            eager_unfolding = (uu___102_1089.eager_unfolding);
            inlining = (uu___102_1089.inlining);
            no_delta_steps = (uu___102_1089.no_delta_steps);
            unfold_until = (uu___102_1089.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___102_1089.unfold_attr);
            unfold_tac = (uu___102_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1089.pure_subterms_within_computations);
            simplify = (uu___102_1089.simplify);
            erase_universes = (uu___102_1089.erase_universes);
            allow_unbound_universes = (uu___102_1089.allow_unbound_universes);
            reify_ = (uu___102_1089.reify_);
            compress_uvars = (uu___102_1089.compress_uvars);
            no_full_norm = (uu___102_1089.no_full_norm);
            check_no_uvars = (uu___102_1089.check_no_uvars);
            unmeta = (uu___102_1089.unmeta);
            unascribe = (uu___102_1089.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___103_1093 = fs  in
          {
            beta = (uu___103_1093.beta);
            iota = (uu___103_1093.iota);
            zeta = (uu___103_1093.zeta);
            weak = (uu___103_1093.weak);
            hnf = (uu___103_1093.hnf);
            primops = (uu___103_1093.primops);
            eager_unfolding = (uu___103_1093.eager_unfolding);
            inlining = (uu___103_1093.inlining);
            no_delta_steps = (uu___103_1093.no_delta_steps);
            unfold_until = (uu___103_1093.unfold_until);
            unfold_only = (uu___103_1093.unfold_only);
            unfold_attr = (FStar_Pervasives_Native.Some attr);
            unfold_tac = (uu___103_1093.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1093.pure_subterms_within_computations);
            simplify = (uu___103_1093.simplify);
            erase_universes = (uu___103_1093.erase_universes);
            allow_unbound_universes = (uu___103_1093.allow_unbound_universes);
            reify_ = (uu___103_1093.reify_);
            compress_uvars = (uu___103_1093.compress_uvars);
            no_full_norm = (uu___103_1093.no_full_norm);
            check_no_uvars = (uu___103_1093.check_no_uvars);
            unmeta = (uu___103_1093.unmeta);
            unascribe = (uu___103_1093.unascribe)
          }
      | UnfoldTac  ->
          let uu___104_1094 = fs  in
          {
            beta = (uu___104_1094.beta);
            iota = (uu___104_1094.iota);
            zeta = (uu___104_1094.zeta);
            weak = (uu___104_1094.weak);
            hnf = (uu___104_1094.hnf);
            primops = (uu___104_1094.primops);
            eager_unfolding = (uu___104_1094.eager_unfolding);
            inlining = (uu___104_1094.inlining);
            no_delta_steps = (uu___104_1094.no_delta_steps);
            unfold_until = (uu___104_1094.unfold_until);
            unfold_only = (uu___104_1094.unfold_only);
            unfold_attr = (uu___104_1094.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___104_1094.pure_subterms_within_computations);
            simplify = (uu___104_1094.simplify);
            erase_universes = (uu___104_1094.erase_universes);
            allow_unbound_universes = (uu___104_1094.allow_unbound_universes);
            reify_ = (uu___104_1094.reify_);
            compress_uvars = (uu___104_1094.compress_uvars);
            no_full_norm = (uu___104_1094.no_full_norm);
            check_no_uvars = (uu___104_1094.check_no_uvars);
            unmeta = (uu___104_1094.unmeta);
            unascribe = (uu___104_1094.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___105_1095 = fs  in
          {
            beta = (uu___105_1095.beta);
            iota = (uu___105_1095.iota);
            zeta = (uu___105_1095.zeta);
            weak = (uu___105_1095.weak);
            hnf = (uu___105_1095.hnf);
            primops = (uu___105_1095.primops);
            eager_unfolding = (uu___105_1095.eager_unfolding);
            inlining = (uu___105_1095.inlining);
            no_delta_steps = (uu___105_1095.no_delta_steps);
            unfold_until = (uu___105_1095.unfold_until);
            unfold_only = (uu___105_1095.unfold_only);
            unfold_attr = (uu___105_1095.unfold_attr);
            unfold_tac = (uu___105_1095.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___105_1095.simplify);
            erase_universes = (uu___105_1095.erase_universes);
            allow_unbound_universes = (uu___105_1095.allow_unbound_universes);
            reify_ = (uu___105_1095.reify_);
            compress_uvars = (uu___105_1095.compress_uvars);
            no_full_norm = (uu___105_1095.no_full_norm);
            check_no_uvars = (uu___105_1095.check_no_uvars);
            unmeta = (uu___105_1095.unmeta);
            unascribe = (uu___105_1095.unascribe)
          }
      | Simplify  ->
          let uu___106_1096 = fs  in
          {
            beta = (uu___106_1096.beta);
            iota = (uu___106_1096.iota);
            zeta = (uu___106_1096.zeta);
            weak = (uu___106_1096.weak);
            hnf = (uu___106_1096.hnf);
            primops = (uu___106_1096.primops);
            eager_unfolding = (uu___106_1096.eager_unfolding);
            inlining = (uu___106_1096.inlining);
            no_delta_steps = (uu___106_1096.no_delta_steps);
            unfold_until = (uu___106_1096.unfold_until);
            unfold_only = (uu___106_1096.unfold_only);
            unfold_attr = (uu___106_1096.unfold_attr);
            unfold_tac = (uu___106_1096.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1096.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___106_1096.erase_universes);
            allow_unbound_universes = (uu___106_1096.allow_unbound_universes);
            reify_ = (uu___106_1096.reify_);
            compress_uvars = (uu___106_1096.compress_uvars);
            no_full_norm = (uu___106_1096.no_full_norm);
            check_no_uvars = (uu___106_1096.check_no_uvars);
            unmeta = (uu___106_1096.unmeta);
            unascribe = (uu___106_1096.unascribe)
          }
      | EraseUniverses  ->
          let uu___107_1097 = fs  in
          {
            beta = (uu___107_1097.beta);
            iota = (uu___107_1097.iota);
            zeta = (uu___107_1097.zeta);
            weak = (uu___107_1097.weak);
            hnf = (uu___107_1097.hnf);
            primops = (uu___107_1097.primops);
            eager_unfolding = (uu___107_1097.eager_unfolding);
            inlining = (uu___107_1097.inlining);
            no_delta_steps = (uu___107_1097.no_delta_steps);
            unfold_until = (uu___107_1097.unfold_until);
            unfold_only = (uu___107_1097.unfold_only);
            unfold_attr = (uu___107_1097.unfold_attr);
            unfold_tac = (uu___107_1097.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1097.pure_subterms_within_computations);
            simplify = (uu___107_1097.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___107_1097.allow_unbound_universes);
            reify_ = (uu___107_1097.reify_);
            compress_uvars = (uu___107_1097.compress_uvars);
            no_full_norm = (uu___107_1097.no_full_norm);
            check_no_uvars = (uu___107_1097.check_no_uvars);
            unmeta = (uu___107_1097.unmeta);
            unascribe = (uu___107_1097.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___108_1098 = fs  in
          {
            beta = (uu___108_1098.beta);
            iota = (uu___108_1098.iota);
            zeta = (uu___108_1098.zeta);
            weak = (uu___108_1098.weak);
            hnf = (uu___108_1098.hnf);
            primops = (uu___108_1098.primops);
            eager_unfolding = (uu___108_1098.eager_unfolding);
            inlining = (uu___108_1098.inlining);
            no_delta_steps = (uu___108_1098.no_delta_steps);
            unfold_until = (uu___108_1098.unfold_until);
            unfold_only = (uu___108_1098.unfold_only);
            unfold_attr = (uu___108_1098.unfold_attr);
            unfold_tac = (uu___108_1098.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1098.pure_subterms_within_computations);
            simplify = (uu___108_1098.simplify);
            erase_universes = (uu___108_1098.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___108_1098.reify_);
            compress_uvars = (uu___108_1098.compress_uvars);
            no_full_norm = (uu___108_1098.no_full_norm);
            check_no_uvars = (uu___108_1098.check_no_uvars);
            unmeta = (uu___108_1098.unmeta);
            unascribe = (uu___108_1098.unascribe)
          }
      | Reify  ->
          let uu___109_1099 = fs  in
          {
            beta = (uu___109_1099.beta);
            iota = (uu___109_1099.iota);
            zeta = (uu___109_1099.zeta);
            weak = (uu___109_1099.weak);
            hnf = (uu___109_1099.hnf);
            primops = (uu___109_1099.primops);
            eager_unfolding = (uu___109_1099.eager_unfolding);
            inlining = (uu___109_1099.inlining);
            no_delta_steps = (uu___109_1099.no_delta_steps);
            unfold_until = (uu___109_1099.unfold_until);
            unfold_only = (uu___109_1099.unfold_only);
            unfold_attr = (uu___109_1099.unfold_attr);
            unfold_tac = (uu___109_1099.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1099.pure_subterms_within_computations);
            simplify = (uu___109_1099.simplify);
            erase_universes = (uu___109_1099.erase_universes);
            allow_unbound_universes = (uu___109_1099.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___109_1099.compress_uvars);
            no_full_norm = (uu___109_1099.no_full_norm);
            check_no_uvars = (uu___109_1099.check_no_uvars);
            unmeta = (uu___109_1099.unmeta);
            unascribe = (uu___109_1099.unascribe)
          }
      | CompressUvars  ->
          let uu___110_1100 = fs  in
          {
            beta = (uu___110_1100.beta);
            iota = (uu___110_1100.iota);
            zeta = (uu___110_1100.zeta);
            weak = (uu___110_1100.weak);
            hnf = (uu___110_1100.hnf);
            primops = (uu___110_1100.primops);
            eager_unfolding = (uu___110_1100.eager_unfolding);
            inlining = (uu___110_1100.inlining);
            no_delta_steps = (uu___110_1100.no_delta_steps);
            unfold_until = (uu___110_1100.unfold_until);
            unfold_only = (uu___110_1100.unfold_only);
            unfold_attr = (uu___110_1100.unfold_attr);
            unfold_tac = (uu___110_1100.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1100.pure_subterms_within_computations);
            simplify = (uu___110_1100.simplify);
            erase_universes = (uu___110_1100.erase_universes);
            allow_unbound_universes = (uu___110_1100.allow_unbound_universes);
            reify_ = (uu___110_1100.reify_);
            compress_uvars = true;
            no_full_norm = (uu___110_1100.no_full_norm);
            check_no_uvars = (uu___110_1100.check_no_uvars);
            unmeta = (uu___110_1100.unmeta);
            unascribe = (uu___110_1100.unascribe)
          }
      | NoFullNorm  ->
          let uu___111_1101 = fs  in
          {
            beta = (uu___111_1101.beta);
            iota = (uu___111_1101.iota);
            zeta = (uu___111_1101.zeta);
            weak = (uu___111_1101.weak);
            hnf = (uu___111_1101.hnf);
            primops = (uu___111_1101.primops);
            eager_unfolding = (uu___111_1101.eager_unfolding);
            inlining = (uu___111_1101.inlining);
            no_delta_steps = (uu___111_1101.no_delta_steps);
            unfold_until = (uu___111_1101.unfold_until);
            unfold_only = (uu___111_1101.unfold_only);
            unfold_attr = (uu___111_1101.unfold_attr);
            unfold_tac = (uu___111_1101.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1101.pure_subterms_within_computations);
            simplify = (uu___111_1101.simplify);
            erase_universes = (uu___111_1101.erase_universes);
            allow_unbound_universes = (uu___111_1101.allow_unbound_universes);
            reify_ = (uu___111_1101.reify_);
            compress_uvars = (uu___111_1101.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___111_1101.check_no_uvars);
            unmeta = (uu___111_1101.unmeta);
            unascribe = (uu___111_1101.unascribe)
          }
      | CheckNoUvars  ->
          let uu___112_1102 = fs  in
          {
            beta = (uu___112_1102.beta);
            iota = (uu___112_1102.iota);
            zeta = (uu___112_1102.zeta);
            weak = (uu___112_1102.weak);
            hnf = (uu___112_1102.hnf);
            primops = (uu___112_1102.primops);
            eager_unfolding = (uu___112_1102.eager_unfolding);
            inlining = (uu___112_1102.inlining);
            no_delta_steps = (uu___112_1102.no_delta_steps);
            unfold_until = (uu___112_1102.unfold_until);
            unfold_only = (uu___112_1102.unfold_only);
            unfold_attr = (uu___112_1102.unfold_attr);
            unfold_tac = (uu___112_1102.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1102.pure_subterms_within_computations);
            simplify = (uu___112_1102.simplify);
            erase_universes = (uu___112_1102.erase_universes);
            allow_unbound_universes = (uu___112_1102.allow_unbound_universes);
            reify_ = (uu___112_1102.reify_);
            compress_uvars = (uu___112_1102.compress_uvars);
            no_full_norm = (uu___112_1102.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___112_1102.unmeta);
            unascribe = (uu___112_1102.unascribe)
          }
      | Unmeta  ->
          let uu___113_1103 = fs  in
          {
            beta = (uu___113_1103.beta);
            iota = (uu___113_1103.iota);
            zeta = (uu___113_1103.zeta);
            weak = (uu___113_1103.weak);
            hnf = (uu___113_1103.hnf);
            primops = (uu___113_1103.primops);
            eager_unfolding = (uu___113_1103.eager_unfolding);
            inlining = (uu___113_1103.inlining);
            no_delta_steps = (uu___113_1103.no_delta_steps);
            unfold_until = (uu___113_1103.unfold_until);
            unfold_only = (uu___113_1103.unfold_only);
            unfold_attr = (uu___113_1103.unfold_attr);
            unfold_tac = (uu___113_1103.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1103.pure_subterms_within_computations);
            simplify = (uu___113_1103.simplify);
            erase_universes = (uu___113_1103.erase_universes);
            allow_unbound_universes = (uu___113_1103.allow_unbound_universes);
            reify_ = (uu___113_1103.reify_);
            compress_uvars = (uu___113_1103.compress_uvars);
            no_full_norm = (uu___113_1103.no_full_norm);
            check_no_uvars = (uu___113_1103.check_no_uvars);
            unmeta = true;
            unascribe = (uu___113_1103.unascribe)
          }
      | Unascribe  ->
          let uu___114_1104 = fs  in
          {
            beta = (uu___114_1104.beta);
            iota = (uu___114_1104.iota);
            zeta = (uu___114_1104.zeta);
            weak = (uu___114_1104.weak);
            hnf = (uu___114_1104.hnf);
            primops = (uu___114_1104.primops);
            eager_unfolding = (uu___114_1104.eager_unfolding);
            inlining = (uu___114_1104.inlining);
            no_delta_steps = (uu___114_1104.no_delta_steps);
            unfold_until = (uu___114_1104.unfold_until);
            unfold_only = (uu___114_1104.unfold_only);
            unfold_attr = (uu___114_1104.unfold_attr);
            unfold_tac = (uu___114_1104.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1104.pure_subterms_within_computations);
            simplify = (uu___114_1104.simplify);
            erase_universes = (uu___114_1104.erase_universes);
            allow_unbound_universes = (uu___114_1104.allow_unbound_universes);
            reify_ = (uu___114_1104.reify_);
            compress_uvars = (uu___114_1104.compress_uvars);
            no_full_norm = (uu___114_1104.no_full_norm);
            check_no_uvars = (uu___114_1104.check_no_uvars);
            unmeta = (uu___114_1104.unmeta);
            unascribe = true
          }
       in
    FStar_List.fold_right add_one1 s default_steps
  
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1136  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }[@@deriving show]
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
  
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy [@@deriving show]
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1337 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1439 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1450 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___72_1469  ->
    match uu___72_1469 with
    | Clos (uu____1470,t,uu____1472,uu____1473) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1518 -> "Univ"
    | Dummy  -> "dummy"
  
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  b380: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__print_normalized
  
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step Prims.list ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool }[@@deriving show]
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps : cfg -> primitive_step Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
  
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo 
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____1884 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____1920 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____1956 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2025 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2067 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2123 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2163 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2195 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2231 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2247 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____2272 .
    'Auu____2272 ->
      FStar_Range.range -> 'Auu____2272 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2326 = FStar_ST.op_Bang r  in
          match uu____2326 with
          | FStar_Pervasives_Native.Some uu____2374 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2428 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2428 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___73_2435  ->
    match uu___73_2435 with
    | Arg (c,uu____2437,uu____2438) ->
        let uu____2439 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2439
    | MemoLazy uu____2440 -> "MemoLazy"
    | Abs (uu____2447,bs,uu____2449,uu____2450,uu____2451) ->
        let uu____2456 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2456
    | UnivArgs uu____2461 -> "UnivArgs"
    | Match uu____2468 -> "Match"
    | App (uu____2475,t,uu____2477,uu____2478) ->
        let uu____2479 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2479
    | Meta (m,uu____2481) -> "Meta"
    | Let uu____2482 -> "Let"
    | Cfg uu____2491 -> "Cfg"
    | Debug (t,uu____2493) ->
        let uu____2494 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2494
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2502 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2502 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2533 . 'Auu____2533 Prims.list -> Prims.bool =
  fun uu___74_2539  ->
    match uu___74_2539 with | [] -> true | uu____2542 -> false
  
let lookup_bvar :
  'Auu____2549 'Auu____2550 .
    ('Auu____2550,'Auu____2549) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2549
  =
  fun env  ->
    fun x  ->
      try
        let uu____2574 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2574
      with
      | uu____2587 ->
          let uu____2588 =
            let uu____2589 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2589  in
          failwith uu____2588
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____2626 =
            FStar_List.fold_left
              (fun uu____2652  ->
                 fun u1  ->
                   match uu____2652 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2677 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2677 with
                        | (k_u,n1) ->
                            let uu____2692 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2692
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2626 with
          | (uu____2710,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2735 =
                   let uu____2736 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2736  in
                 match uu____2735 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2754 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2762 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2768 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2777 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2786 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2793 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2793 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2810 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2810 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2818 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2826 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2826 with
                                  | (uu____2831,m) -> n1 <= m))
                           in
                        if uu____2818 then rest1 else us1
                    | uu____2836 -> us1)
               | uu____2841 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2845 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2845
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2849 = aux u  in
           match uu____2849 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____2953  ->
             let uu____2954 = FStar_Syntax_Print.tag_of_term t  in
             let uu____2955 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2954
               uu____2955);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____2962 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2964 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2989 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2990 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2991 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2992 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3009 =
                      let uu____3010 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3011 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3010 uu____3011
                       in
                    failwith uu____3009
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3014 =
                    let uu____3015 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3015  in
                  mk uu____3014 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3022 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3022
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3024 = lookup_bvar env x  in
                  (match uu____3024 with
                   | Univ uu____3027 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3030,uu____3031) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3143 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3143 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3171 =
                         let uu____3172 =
                           let uu____3189 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3189)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3172  in
                       mk uu____3171 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3220 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3220 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3262 =
                    let uu____3273 =
                      let uu____3280 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3280]  in
                    closures_as_binders_delayed cfg env uu____3273  in
                  (match uu____3262 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3298 =
                         let uu____3299 =
                           let uu____3306 =
                             let uu____3307 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3307
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3306, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3299  in
                       mk uu____3298 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3398 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3398
                    | FStar_Util.Inr c ->
                        let uu____3412 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3412
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3428 =
                    let uu____3429 =
                      let uu____3456 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3456, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3429  in
                  mk uu____3428 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3507 =
                    let uu____3508 =
                      let uu____3515 = closure_as_term_delayed cfg env t'  in
                      let uu____3518 =
                        let uu____3519 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3519  in
                      (uu____3515, uu____3518)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3508  in
                  mk uu____3507 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3579 =
                    let uu____3580 =
                      let uu____3587 = closure_as_term_delayed cfg env t'  in
                      let uu____3590 =
                        let uu____3591 =
                          let uu____3598 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3598)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3591  in
                      (uu____3587, uu____3590)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3580  in
                  mk uu____3579 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3617 =
                    let uu____3618 =
                      let uu____3625 = closure_as_term_delayed cfg env t'  in
                      let uu____3628 =
                        let uu____3629 =
                          let uu____3638 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3638)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3629  in
                      (uu____3625, uu____3628)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3618  in
                  mk uu____3617 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3651 =
                    let uu____3652 =
                      let uu____3659 = closure_as_term_delayed cfg env t'  in
                      (uu____3659, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3652  in
                  mk uu____3651 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3699  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3718 =
                    let uu____3729 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3729
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3748 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___119_3760 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_3760.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_3760.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3748))
                     in
                  (match uu____3718 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___120_3776 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___120_3776.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___120_3776.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3787,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3846  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3871 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3871
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3891  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____3913 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3913
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___121_3925 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_3925.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_3925.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___122_3926 = lb  in
                    let uu____3927 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___122_3926.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___122_3926.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3927
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3957  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4046 =
                    match uu____4046 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4101 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4122 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4182  ->
                                        fun uu____4183  ->
                                          match (uu____4182, uu____4183) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4274 =
                                                norm_pat env3 p1  in
                                              (match uu____4274 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4122 with
                               | (pats1,env3) ->
                                   ((let uu___123_4356 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___123_4356.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___124_4375 = x  in
                                let uu____4376 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___124_4375.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___124_4375.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4376
                                }  in
                              ((let uu___125_4390 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___125_4390.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___126_4401 = x  in
                                let uu____4402 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___126_4401.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___126_4401.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4402
                                }  in
                              ((let uu___127_4416 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___127_4416.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___128_4432 = x  in
                                let uu____4433 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___128_4432.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___128_4432.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4433
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___129_4440 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___129_4440.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4443 = norm_pat env1 pat  in
                        (match uu____4443 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4472 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4472
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4478 =
                    let uu____4479 =
                      let uu____4502 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4502)  in
                    FStar_Syntax_Syntax.Tm_match uu____4479  in
                  mk uu____4478 t1.FStar_Syntax_Syntax.pos))

and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4588 -> closure_as_term cfg env t

and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4614 ->
            FStar_List.map
              (fun uu____4631  ->
                 match uu____4631 with
                 | (x,imp) ->
                     let uu____4650 = closure_as_term_delayed cfg env x  in
                     (uu____4650, imp)) args

and (closures_as_binders_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4664 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4713  ->
                  fun uu____4714  ->
                    match (uu____4713, uu____4714) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___130_4784 = b  in
                          let uu____4785 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___130_4784.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___130_4784.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4785
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4664 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____4878 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4891 = closure_as_term_delayed cfg env t  in
                 let uu____4892 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4891 uu____4892
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4905 = closure_as_term_delayed cfg env t  in
                 let uu____4906 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4905 uu____4906
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___75_4932  ->
                           match uu___75_4932 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4936 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____4936
                           | f -> f))
                    in
                 let uu____4940 =
                   let uu___131_4941 = c1  in
                   let uu____4942 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4942;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___131_4941.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4940)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_4952  ->
            match uu___76_4952 with
            | FStar_Syntax_Syntax.DECREASES uu____4953 -> false
            | uu____4956 -> true))

and (close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___77_4974  ->
                      match uu___77_4974 with
                      | FStar_Syntax_Syntax.DECREASES uu____4975 -> false
                      | uu____4978 -> true))
               in
            let rc1 =
              let uu___132_4980 = rc  in
              let uu____4981 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___132_4980.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4981;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4988 -> lopt

let (built_in_primitive_steps : primitive_step Prims.list) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe
     in
  let arg_as_list a u a =
    let uu____5073 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5073  in
  let arg_as_bounded_int uu____5101 =
    match uu____5101 with
    | (a,uu____5113) ->
        let uu____5120 =
          let uu____5121 = FStar_Syntax_Subst.compress a  in
          uu____5121.FStar_Syntax_Syntax.n  in
        (match uu____5120 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5131;
                FStar_Syntax_Syntax.vars = uu____5132;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5134;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5135;_},uu____5136)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5175 =
               let uu____5180 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5180)  in
             FStar_Pervasives_Native.Some uu____5175
         | uu____5185 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5225 = f a  in FStar_Pervasives_Native.Some uu____5225
    | uu____5226 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5274 = f a0 a1  in FStar_Pervasives_Native.Some uu____5274
    | uu____5275 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5317 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5317)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5366 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5366)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5390 =
    match uu____5390 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5438 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5438)) a429 a430)
     in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5466 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5466)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5487 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5487)) a436
             a437)
     in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5515 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5515)) a439
               a440 a441)
     in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5543 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5543))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5651 =
          let uu____5660 = as_a a  in
          let uu____5663 = as_b b  in (uu____5660, uu____5663)  in
        (match uu____5651 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5678 =
               let uu____5679 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5679  in
             FStar_Pervasives_Native.Some uu____5678
         | uu____5680 -> FStar_Pervasives_Native.None)
    | uu____5689 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5703 =
        let uu____5704 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5704  in
      mk uu____5703 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5714 =
      let uu____5717 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5717  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5714  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5749 =
      let uu____5750 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5750  in
    FStar_Syntax_Embeddings.embed_int rng uu____5749  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5768 = arg_as_string a1  in
        (match uu____5768 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5774 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5774 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5787 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5787
              | uu____5788 -> FStar_Pervasives_Native.None)
         | uu____5793 -> FStar_Pervasives_Native.None)
    | uu____5796 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5806 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5806  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5830 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5841 =
          let uu____5862 = arg_as_string fn  in
          let uu____5865 = arg_as_int from_line  in
          let uu____5868 = arg_as_int from_col  in
          let uu____5871 = arg_as_int to_line  in
          let uu____5874 = arg_as_int to_col  in
          (uu____5862, uu____5865, uu____5868, uu____5871, uu____5874)  in
        (match uu____5841 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5905 =
                 let uu____5906 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5907 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5906 uu____5907  in
               let uu____5908 =
                 let uu____5909 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5910 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5909 uu____5910  in
               FStar_Range.mk_range fn1 uu____5905 uu____5908  in
             let uu____5911 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____5911
         | uu____5916 -> FStar_Pervasives_Native.None)
    | uu____5937 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5964)::(a1,uu____5966)::(a2,uu____5968)::[] ->
        let uu____6005 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6005 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6018 -> FStar_Pervasives_Native.None)
    | uu____6019 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6046)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6055 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6079 =
      let uu____6094 =
        let uu____6109 =
          let uu____6124 =
            let uu____6139 =
              let uu____6154 =
                let uu____6169 =
                  let uu____6184 =
                    let uu____6199 =
                      let uu____6214 =
                        let uu____6229 =
                          let uu____6244 =
                            let uu____6259 =
                              let uu____6274 =
                                let uu____6289 =
                                  let uu____6304 =
                                    let uu____6319 =
                                      let uu____6334 =
                                        let uu____6349 =
                                          let uu____6364 =
                                            let uu____6379 =
                                              let uu____6394 =
                                                let uu____6407 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6407,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448)))
                                                 in
                                              let uu____6414 =
                                                let uu____6429 =
                                                  let uu____6442 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6442,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451)))
                                                   in
                                                let uu____6449 =
                                                  let uu____6464 =
                                                    let uu____6479 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6479,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6488 =
                                                    let uu____6505 =
                                                      let uu____6520 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6520,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6529 =
                                                      let uu____6546 =
                                                        let uu____6565 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6565,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6546]  in
                                                    uu____6505 :: uu____6529
                                                     in
                                                  uu____6464 :: uu____6488
                                                   in
                                                uu____6429 :: uu____6449  in
                                              uu____6394 :: uu____6414  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6379
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6364
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____6349
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____6334
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____6319
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6782 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6782 y)) a466
                                                a467 a468)))
                                    :: uu____6304
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6289
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6274
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6259
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6244
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6229
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6214
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____6949 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____6949)) a470 a471 a472)))
                      :: uu____6199
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____6975 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____6975)) a474 a475 a476)))
                    :: uu____6184
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7001 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7001)) a478 a479 a480)))
                  :: uu____6169
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7027 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7027)) a482 a483 a484)))
                :: uu____6154
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6139
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6124
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6109
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6094
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6079
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7180 =
        let uu____7181 =
          let uu____7182 = FStar_Syntax_Syntax.as_arg c  in [uu____7182]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7181  in
      uu____7180 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7232 =
                let uu____7245 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7245, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7261  ->
                                    fun uu____7262  ->
                                      match (uu____7261, uu____7262) with
                                      | ((int_to_t1,x),(uu____7281,y)) ->
                                          let uu____7291 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7291)) a486 a487 a488)))
                 in
              let uu____7292 =
                let uu____7307 =
                  let uu____7320 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7320, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7336  ->
                                      fun uu____7337  ->
                                        match (uu____7336, uu____7337) with
                                        | ((int_to_t1,x),(uu____7356,y)) ->
                                            let uu____7366 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7366)) a490 a491 a492)))
                   in
                let uu____7367 =
                  let uu____7382 =
                    let uu____7395 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7395, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7411  ->
                                        fun uu____7412  ->
                                          match (uu____7411, uu____7412) with
                                          | ((int_to_t1,x),(uu____7431,y)) ->
                                              let uu____7441 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7441)) a494 a495 a496)))
                     in
                  let uu____7442 =
                    let uu____7457 =
                      let uu____7470 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7470, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7482  ->
                                        match uu____7482 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7457]  in
                  uu____7382 :: uu____7442  in
                uu____7307 :: uu____7367  in
              uu____7232 :: uu____7292))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7596 =
                let uu____7609 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7609, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7625  ->
                                    fun uu____7626  ->
                                      match (uu____7625, uu____7626) with
                                      | ((int_to_t1,x),(uu____7645,y)) ->
                                          let uu____7655 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7655)) a501 a502 a503)))
                 in
              let uu____7656 =
                let uu____7671 =
                  let uu____7684 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7684, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7700  ->
                                      fun uu____7701  ->
                                        match (uu____7700, uu____7701) with
                                        | ((int_to_t1,x),(uu____7720,y)) ->
                                            let uu____7730 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7730)) a505 a506 a507)))
                   in
                [uu____7671]  in
              uu____7596 :: uu____7656))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let (equality_ops : primitive_step Prims.list) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7820)::(a1,uu____7822)::(a2,uu____7824)::[] ->
        let uu____7861 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7861 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___133_7867 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___133_7867.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___133_7867.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___134_7871 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___134_7871.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___134_7871.FStar_Syntax_Syntax.vars)
                })
         | uu____7872 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7874)::uu____7875::(a1,uu____7877)::(a2,uu____7879)::[] ->
        let uu____7928 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7928 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___133_7934 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___133_7934.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___133_7934.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___134_7938 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___134_7938.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___134_7938.FStar_Syntax_Syntax.vars)
                })
         | uu____7939 -> FStar_Pervasives_Native.None)
    | uu____7940 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  [propositional_equality; hetero_propositional_equality] 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____7959 =
        let uu____7960 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____7960 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____7959
    with | uu____7966 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____7970 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7970) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8030  ->
           fun subst1  ->
             match uu____8030 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8071,uu____8072)) ->
                      let uu____8131 = b  in
                      (match uu____8131 with
                       | (bv,uu____8139) ->
                           let uu____8140 =
                             let uu____8141 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____8141  in
                           if uu____8140
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8146 = unembed_binder term1  in
                              match uu____8146 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8153 =
                                      let uu___137_8154 = bv  in
                                      let uu____8155 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___137_8154.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___137_8154.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8155
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8153
                                     in
                                  let b_for_x =
                                    let uu____8159 =
                                      let uu____8166 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8166)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8159  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_8175  ->
                                         match uu___78_8175 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8176,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8178;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8179;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8184 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8185 -> subst1)) env []
  
let reduce_primops :
  'Auu____8202 'Auu____8203 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8203) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8202 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____8244 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).primops  in
          if uu____8244
          then tm
          else
            (let uu____8246 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8246 with
             | (head1,args) ->
                 let uu____8283 =
                   let uu____8284 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8284.FStar_Syntax_Syntax.n  in
                 (match uu____8283 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8288 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps
                         in
                      (match uu____8288 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8305  ->
                                   let uu____8306 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8307 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8314 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8306 uu____8307 uu____8314);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8319  ->
                                   let uu____8320 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8320);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8323  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8325 =
                                 prim_step.interpretation psc args  in
                               match uu____8325 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8331  ->
                                         let uu____8332 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8332);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8338  ->
                                         let uu____8339 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8340 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8339 uu____8340);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8341 ->
                           (log_primops cfg
                              (fun uu____8345  ->
                                 let uu____8346 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8346);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8350  ->
                            let uu____8351 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8351);
                       (match args with
                        | (a1,uu____8353)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8370 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8382  ->
                            let uu____8383 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8383);
                       (match args with
                        | (t,uu____8385)::(r,uu____8387)::[] ->
                            let uu____8414 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8414 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___138_8418 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___138_8418.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___138_8418.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8421 -> tm))
                  | uu____8430 -> tm))
  
let reduce_equality :
  'Auu____8435 'Auu____8436 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8436) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8435 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___139_8474 = cfg  in
         {
           steps =
             (let uu___140_8477 = default_steps  in
              {
                beta = (uu___140_8477.beta);
                iota = (uu___140_8477.iota);
                zeta = (uu___140_8477.zeta);
                weak = (uu___140_8477.weak);
                hnf = (uu___140_8477.hnf);
                primops = true;
                eager_unfolding = (uu___140_8477.eager_unfolding);
                inlining = (uu___140_8477.inlining);
                no_delta_steps = (uu___140_8477.no_delta_steps);
                unfold_until = (uu___140_8477.unfold_until);
                unfold_only = (uu___140_8477.unfold_only);
                unfold_attr = (uu___140_8477.unfold_attr);
                unfold_tac = (uu___140_8477.unfold_tac);
                pure_subterms_within_computations =
                  (uu___140_8477.pure_subterms_within_computations);
                simplify = (uu___140_8477.simplify);
                erase_universes = (uu___140_8477.erase_universes);
                allow_unbound_universes =
                  (uu___140_8477.allow_unbound_universes);
                reify_ = (uu___140_8477.reify_);
                compress_uvars = (uu___140_8477.compress_uvars);
                no_full_norm = (uu___140_8477.no_full_norm);
                check_no_uvars = (uu___140_8477.check_no_uvars);
                unmeta = (uu___140_8477.unmeta);
                unascribe = (uu___140_8477.unascribe)
              });
           tcenv = (uu___139_8474.tcenv);
           debug = (uu___139_8474.debug);
           delta_level = (uu___139_8474.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___139_8474.strong);
           memoize_lazy = (uu___139_8474.memoize_lazy);
           normalize_pure_lets = (uu___139_8474.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8484 'Auu____8485 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8485) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8484 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8527 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8527
          then tm1
          else
            (let w t =
               let uu___141_8539 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___141_8539.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___141_8539.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8555;
                      FStar_Syntax_Syntax.vars = uu____8556;_},uu____8557)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8564;
                      FStar_Syntax_Syntax.vars = uu____8565;_},uu____8566)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8572 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8577 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8577
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8598 =
                 match uu____8598 with
                 | (t1,q) ->
                     let uu____8611 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8611 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8639 -> (t1, q))
                  in
               let uu____8648 = FStar_Syntax_Util.head_and_args t  in
               match uu____8648 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg)  in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8745;
                         FStar_Syntax_Syntax.vars = uu____8746;_},uu____8747);
                    FStar_Syntax_Syntax.pos = uu____8748;
                    FStar_Syntax_Syntax.vars = uu____8749;_},args)
                 ->
                 let uu____8775 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8775
                 then
                   let uu____8776 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8776 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8831)::
                        (uu____8832,(arg,uu____8834))::[] ->
                        maybe_auto_squash arg
                    | (uu____8899,(arg,uu____8901))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8902)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8967)::uu____8968::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9031::(FStar_Pervasives_Native.Some (false
                                   ),uu____9032)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9095 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9111 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9111
                    then
                      let uu____9112 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9112 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9167)::uu____9168::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9231::(FStar_Pervasives_Native.Some (true
                                     ),uu____9232)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9295)::
                          (uu____9296,(arg,uu____9298))::[] ->
                          maybe_auto_squash arg
                      | (uu____9363,(arg,uu____9365))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9366)::[]
                          -> maybe_auto_squash arg
                      | uu____9431 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9447 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9447
                       then
                         let uu____9448 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9448 with
                         | uu____9503::(FStar_Pervasives_Native.Some (true
                                        ),uu____9504)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9567)::uu____9568::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9631)::
                             (uu____9632,(arg,uu____9634))::[] ->
                             maybe_auto_squash arg
                         | (uu____9699,(p,uu____9701))::(uu____9702,(q,uu____9704))::[]
                             ->
                             let uu____9769 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9769
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9771 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9787 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9787
                          then
                            let uu____9788 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9788 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9843)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9882)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9921 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____9937 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____9937
                             then
                               match args with
                               | (t,uu____9939)::[] ->
                                   let uu____9956 =
                                     let uu____9957 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____9957.FStar_Syntax_Syntax.n  in
                                   (match uu____9956 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9960::[],body,uu____9962) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9989 -> tm1)
                                    | uu____9992 -> tm1)
                               | (uu____9993,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9994))::
                                   (t,uu____9996)::[] ->
                                   let uu____10035 =
                                     let uu____10036 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10036.FStar_Syntax_Syntax.n  in
                                   (match uu____10035 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10039::[],body,uu____10041) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10068 -> tm1)
                                    | uu____10071 -> tm1)
                               | uu____10072 -> tm1
                             else
                               (let uu____10082 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10082
                                then
                                  match args with
                                  | (t,uu____10084)::[] ->
                                      let uu____10101 =
                                        let uu____10102 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10102.FStar_Syntax_Syntax.n  in
                                      (match uu____10101 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10105::[],body,uu____10107)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10134 -> tm1)
                                       | uu____10137 -> tm1)
                                  | (uu____10138,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10139))::(t,uu____10141)::[] ->
                                      let uu____10180 =
                                        let uu____10181 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10181.FStar_Syntax_Syntax.n  in
                                      (match uu____10180 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10184::[],body,uu____10186)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10213 -> tm1)
                                       | uu____10216 -> tm1)
                                  | uu____10217 -> tm1
                                else
                                  (let uu____10227 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10227
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10228;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10229;_},uu____10230)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10247;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10248;_},uu____10249)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10266 -> tm1
                                   else
                                     (let uu____10276 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10276 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10296 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10306;
                    FStar_Syntax_Syntax.vars = uu____10307;_},args)
                 ->
                 let uu____10329 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____10329
                 then
                   let uu____10330 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____10330 with
                    | (FStar_Pervasives_Native.Some (true ),uu____10385)::
                        (uu____10386,(arg,uu____10388))::[] ->
                        maybe_auto_squash arg
                    | (uu____10453,(arg,uu____10455))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____10456)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____10521)::uu____10522::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10585::(FStar_Pervasives_Native.Some (false
                                    ),uu____10586)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10649 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____10665 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____10665
                    then
                      let uu____10666 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____10666 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10721)::uu____10722::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10785::(FStar_Pervasives_Native.Some (true
                                      ),uu____10786)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____10849)::
                          (uu____10850,(arg,uu____10852))::[] ->
                          maybe_auto_squash arg
                      | (uu____10917,(arg,uu____10919))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10920)::[]
                          -> maybe_auto_squash arg
                      | uu____10985 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11001 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11001
                       then
                         let uu____11002 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11002 with
                         | uu____11057::(FStar_Pervasives_Native.Some (true
                                         ),uu____11058)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11121)::uu____11122::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11185)::
                             (uu____11186,(arg,uu____11188))::[] ->
                             maybe_auto_squash arg
                         | (uu____11253,(p,uu____11255))::(uu____11256,
                                                           (q,uu____11258))::[]
                             ->
                             let uu____11323 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____11323
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11325 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____11341 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____11341
                          then
                            let uu____11342 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____11342 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____11397)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____11436)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____11475 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____11491 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____11491
                             then
                               match args with
                               | (t,uu____11493)::[] ->
                                   let uu____11510 =
                                     let uu____11511 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11511.FStar_Syntax_Syntax.n  in
                                   (match uu____11510 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11514::[],body,uu____11516) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11543 -> tm1)
                                    | uu____11546 -> tm1)
                               | (uu____11547,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____11548))::
                                   (t,uu____11550)::[] ->
                                   let uu____11589 =
                                     let uu____11590 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11590.FStar_Syntax_Syntax.n  in
                                   (match uu____11589 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11593::[],body,uu____11595) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11622 -> tm1)
                                    | uu____11625 -> tm1)
                               | uu____11626 -> tm1
                             else
                               (let uu____11636 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____11636
                                then
                                  match args with
                                  | (t,uu____11638)::[] ->
                                      let uu____11655 =
                                        let uu____11656 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11656.FStar_Syntax_Syntax.n  in
                                      (match uu____11655 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11659::[],body,uu____11661)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11688 -> tm1)
                                       | uu____11691 -> tm1)
                                  | (uu____11692,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____11693))::(t,uu____11695)::[] ->
                                      let uu____11734 =
                                        let uu____11735 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11735.FStar_Syntax_Syntax.n  in
                                      (match uu____11734 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11738::[],body,uu____11740)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11767 -> tm1)
                                       | uu____11770 -> tm1)
                                  | uu____11771 -> tm1
                                else
                                  (let uu____11781 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____11781
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11782;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11783;_},uu____11784)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11801;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11802;_},uu____11803)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11820 -> tm1
                                   else
                                     (let uu____11830 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____11830 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____11850 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____11865 -> tm1)
  
let maybe_simplify :
  'Auu____11872 'Auu____11873 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11873) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11872 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____11916 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11917 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____11916
               uu____11917)
          else ();
          tm'
  
let is_norm_request :
  'Auu____11923 .
    FStar_Syntax_Syntax.term -> 'Auu____11923 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11936 =
        let uu____11943 =
          let uu____11944 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11944.FStar_Syntax_Syntax.n  in
        (uu____11943, args)  in
      match uu____11936 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11950::uu____11951::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11955::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11960::uu____11961::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11964 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___79_11975  ->
    match uu___79_11975 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11981 =
          let uu____11984 =
            let uu____11985 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11985  in
          [uu____11984]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____11981
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12001 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____12001) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____12039 =
          let uu____12042 =
            let uu____12047 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____12047 s  in
          FStar_All.pipe_right uu____12042 FStar_Util.must  in
        FStar_All.pipe_right uu____12039 tr_norm_steps  in
      match args with
      | uu____12072::(tm,uu____12074)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____12097)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____12112)::uu____12113::(tm,uu____12115)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____12155 =
              let uu____12158 = full_norm steps  in parse_steps uu____12158
               in
            Beta :: uu____12155  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____12167 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___80_12184  ->
    match uu___80_12184 with
    | (App
        (uu____12187,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12188;
                       FStar_Syntax_Syntax.vars = uu____12189;_},uu____12190,uu____12191))::uu____12192
        -> true
    | uu____12199 -> false
  
let firstn :
  'Auu____12205 .
    Prims.int ->
      'Auu____12205 Prims.list ->
        ('Auu____12205 Prims.list,'Auu____12205 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify : cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____12241,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12242;
                         FStar_Syntax_Syntax.vars = uu____12243;_},uu____12244,uu____12245))::uu____12246
          -> (cfg.steps).reify_
      | uu____12253 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____12395 ->
                   let uu____12420 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12420
               | uu____12421 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12429  ->
               let uu____12430 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12431 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12432 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12439 =
                 let uu____12440 =
                   let uu____12443 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12443
                    in
                 stack_to_string uu____12440  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12430 uu____12431 uu____12432 uu____12439);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12466 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12467 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12468;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12469;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12472;
                 FStar_Syntax_Syntax.fv_delta = uu____12473;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12474;
                 FStar_Syntax_Syntax.fv_delta = uu____12475;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12476);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (cfg.steps).no_delta_steps))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args  in
               let hd2 = closure_as_term cfg env hd1  in
               let t2 =
                 let uu___142_12518 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___142_12518.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___142_12518.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___143_12556 = cfg  in
                 {
                   steps =
                     (let uu___144_12559 = cfg.steps  in
                      {
                        beta = (uu___144_12559.beta);
                        iota = (uu___144_12559.iota);
                        zeta = (uu___144_12559.zeta);
                        weak = (uu___144_12559.weak);
                        hnf = (uu___144_12559.hnf);
                        primops = (uu___144_12559.primops);
                        eager_unfolding = (uu___144_12559.eager_unfolding);
                        inlining = (uu___144_12559.inlining);
                        no_delta_steps = false;
                        unfold_until = (uu___144_12559.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___144_12559.unfold_attr);
                        unfold_tac = (uu___144_12559.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___144_12559.pure_subterms_within_computations);
                        simplify = (uu___144_12559.simplify);
                        erase_universes = (uu___144_12559.erase_universes);
                        allow_unbound_universes =
                          (uu___144_12559.allow_unbound_universes);
                        reify_ = (uu___144_12559.reify_);
                        compress_uvars = (uu___144_12559.compress_uvars);
                        no_full_norm = (uu___144_12559.no_full_norm);
                        check_no_uvars = (uu___144_12559.check_no_uvars);
                        unmeta = (uu___144_12559.unmeta);
                        unascribe = (uu___144_12559.unascribe)
                      });
                   tcenv = (uu___143_12556.tcenv);
                   debug = (uu___143_12556.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___143_12556.primitive_steps);
                   strong = (uu___143_12556.strong);
                   memoize_lazy = (uu___143_12556.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12562 = get_norm_request (norm cfg' env []) args  in
               (match uu____12562 with
                | (s,tm) ->
                    let delta_level =
                      let uu____12578 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___81_12583  ->
                                match uu___81_12583 with
                                | UnfoldUntil uu____12584 -> true
                                | UnfoldOnly uu____12585 -> true
                                | uu____12588 -> false))
                         in
                      if uu____12578
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___145_12593 = cfg  in
                      let uu____12594 = to_fsteps s  in
                      {
                        steps = uu____12594;
                        tcenv = (uu___145_12593.tcenv);
                        debug = (uu___145_12593.debug);
                        delta_level;
                        primitive_steps = (uu___145_12593.primitive_steps);
                        strong = (uu___145_12593.strong);
                        memoize_lazy = (uu___145_12593.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12603 =
                          let uu____12604 =
                            let uu____12609 = FStar_Util.now ()  in
                            (t1, uu____12609)  in
                          Debug uu____12604  in
                        uu____12603 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12613 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12613
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12622 =
                      let uu____12629 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12629, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12622  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____12638 = FStar_Syntax_Syntax.lid_of_fv fv  in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____12638 ->
               let b = should_reify cfg stack  in
               (log cfg
                  (fun uu____12644  ->
                     let uu____12645 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____12646 = FStar_Util.string_of_bool b  in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____12645 uu____12646);
                if b
                then
                  (let uu____12647 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____12647 t1 fv)
                else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___82_12656  ->
                         match uu___82_12656 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l))
                  in
               let should_delta1 =
                 let uu____12659 =
                   (cfg.steps).unfold_tac &&
                     ((((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.and_lid)
                                ||
                                (FStar_Syntax_Syntax.fv_eq_lid f
                                   FStar_Parser_Const.or_lid))
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Parser_Const.imp_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.forall_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.squash_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Parser_Const.exists_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Parser_Const.eq2_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Parser_Const.eq3_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid))
                    in
                 if uu____12659
                 then false
                 else
                   (let attr_eq a a' =
                      let uu____12668 = FStar_Syntax_Util.eq_tm a a'  in
                      match uu____12668 with
                      | FStar_Syntax_Util.Equal  -> true
                      | uu____12669 -> false  in
                    (should_delta &&
                       (match (cfg.steps).unfold_only with
                        | FStar_Pervasives_Native.None  -> true
                        | FStar_Pervasives_Native.Some lids ->
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid f) lids))
                      &&
                      (match (cfg.steps).unfold_attr with
                       | FStar_Pervasives_Native.None  -> true
                       | FStar_Pervasives_Native.Some attr ->
                           let uu____12678 =
                             FStar_TypeChecker_Env.lookup_attrs_of_lid
                               cfg.tcenv
                               (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           (match uu____12678 with
                            | FStar_Pervasives_Native.Some attrs ->
                                FStar_Util.for_some (attr_eq attr) attrs
                            | FStar_Pervasives_Native.None  -> true)))
                  in
               (log cfg
                  (fun uu____12695  ->
                     let uu____12696 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____12697 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos
                        in
                     let uu____12698 =
                       FStar_Util.string_of_bool should_delta1  in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____12696 uu____12697 uu____12698);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12701 = lookup_bvar env x  in
               (match uu____12701 with
                | Univ uu____12704 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12753 = FStar_ST.op_Bang r  in
                      (match uu____12753 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12871  ->
                                 let uu____12872 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12873 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12872
                                   uu____12873);
                            (let uu____12874 =
                               let uu____12875 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____12875.FStar_Syntax_Syntax.n  in
                             match uu____12874 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12878 ->
                                 norm cfg env2 stack t'
                             | uu____12895 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12965)::uu____12966 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12975)::uu____12976 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12986,uu____12987))::stack_rest ->
                    (match c with
                     | Univ uu____12991 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13000 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13021  ->
                                    let uu____13022 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13022);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13062  ->
                                    let uu____13063 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13063);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____13141  ->
                          let uu____13142 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13142);
                     norm cfg env stack1 t1)
                | (Debug uu____13143)::uu____13144 ->
                    if (cfg.steps).weak
                    then
                      let uu____13151 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13151
                    else
                      (let uu____13153 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13153 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13195  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13232 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13232)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___146_13237 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___146_13237.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___146_13237.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13238 -> lopt  in
                           (log cfg
                              (fun uu____13244  ->
                                 let uu____13245 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13245);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___147_13254 = cfg  in
                               {
                                 steps = (uu___147_13254.steps);
                                 tcenv = (uu___147_13254.tcenv);
                                 debug = (uu___147_13254.debug);
                                 delta_level = (uu___147_13254.delta_level);
                                 primitive_steps =
                                   (uu___147_13254.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___147_13254.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___147_13254.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13265)::uu____13266 ->
                    if (cfg.steps).weak
                    then
                      let uu____13273 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13273
                    else
                      (let uu____13275 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13275 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13317  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13354 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13354)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___146_13359 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___146_13359.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___146_13359.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13360 -> lopt  in
                           (log cfg
                              (fun uu____13366  ->
                                 let uu____13367 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13367);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___147_13376 = cfg  in
                               {
                                 steps = (uu___147_13376.steps);
                                 tcenv = (uu___147_13376.tcenv);
                                 debug = (uu___147_13376.debug);
                                 delta_level = (uu___147_13376.delta_level);
                                 primitive_steps =
                                   (uu___147_13376.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___147_13376.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___147_13376.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13387)::uu____13388 ->
                    if (cfg.steps).weak
                    then
                      let uu____13399 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13399
                    else
                      (let uu____13401 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13401 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13443  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13480 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13480)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___146_13485 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___146_13485.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___146_13485.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13486 -> lopt  in
                           (log cfg
                              (fun uu____13492  ->
                                 let uu____13493 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13493);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___147_13502 = cfg  in
                               {
                                 steps = (uu___147_13502.steps);
                                 tcenv = (uu___147_13502.tcenv);
                                 debug = (uu___147_13502.debug);
                                 delta_level = (uu___147_13502.delta_level);
                                 primitive_steps =
                                   (uu___147_13502.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___147_13502.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___147_13502.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13513)::uu____13514 ->
                    if (cfg.steps).weak
                    then
                      let uu____13525 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13525
                    else
                      (let uu____13527 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13527 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13569  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13606 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13606)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___146_13611 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___146_13611.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___146_13611.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13612 -> lopt  in
                           (log cfg
                              (fun uu____13618  ->
                                 let uu____13619 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13619);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___147_13628 = cfg  in
                               {
                                 steps = (uu___147_13628.steps);
                                 tcenv = (uu___147_13628.tcenv);
                                 debug = (uu___147_13628.debug);
                                 delta_level = (uu___147_13628.delta_level);
                                 primitive_steps =
                                   (uu___147_13628.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___147_13628.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___147_13628.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13639)::uu____13640 ->
                    if (cfg.steps).weak
                    then
                      let uu____13655 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13655
                    else
                      (let uu____13657 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13657 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13699  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13736 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13736)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___146_13741 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___146_13741.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___146_13741.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13742 -> lopt  in
                           (log cfg
                              (fun uu____13748  ->
                                 let uu____13749 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13749);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___147_13758 = cfg  in
                               {
                                 steps = (uu___147_13758.steps);
                                 tcenv = (uu___147_13758.tcenv);
                                 debug = (uu___147_13758.debug);
                                 delta_level = (uu___147_13758.delta_level);
                                 primitive_steps =
                                   (uu___147_13758.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___147_13758.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___147_13758.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____13769 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13769
                    else
                      (let uu____13771 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13771 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13813  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13850 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13850)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___146_13855 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___146_13855.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___146_13855.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13856 -> lopt  in
                           (log cfg
                              (fun uu____13862  ->
                                 let uu____13863 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13863);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___147_13872 = cfg  in
                               {
                                 steps = (uu___147_13872.steps);
                                 tcenv = (uu___147_13872.tcenv);
                                 debug = (uu___147_13872.debug);
                                 delta_level = (uu___147_13872.delta_level);
                                 primitive_steps =
                                   (uu___147_13872.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___147_13872.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___147_13872.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____13921  ->
                         fun stack1  ->
                           match uu____13921 with
                           | (a,aq) ->
                               let uu____13933 =
                                 let uu____13934 =
                                   let uu____13941 =
                                     let uu____13942 =
                                       let uu____13973 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13973, false)  in
                                     Clos uu____13942  in
                                   (uu____13941, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13934  in
                               uu____13933 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14057  ->
                     let uu____14058 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14058);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if (cfg.steps).weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___148_14094 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___148_14094.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___148_14094.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14095 ->
                      let uu____14100 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14100)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14103 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14103 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14134 =
                          let uu____14135 =
                            let uu____14142 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___149_14144 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___149_14144.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___149_14144.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14142)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14135  in
                        mk uu____14134 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14163 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14163
               else
                 (let uu____14165 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14165 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14173 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14197  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14173 c1  in
                      let t2 =
                        let uu____14219 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14219 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14330)::uu____14331 ->
                    (log cfg
                       (fun uu____14342  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14343)::uu____14344 ->
                    (log cfg
                       (fun uu____14355  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14356,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14357;
                                   FStar_Syntax_Syntax.vars = uu____14358;_},uu____14359,uu____14360))::uu____14361
                    ->
                    (log cfg
                       (fun uu____14370  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14371)::uu____14372 ->
                    (log cfg
                       (fun uu____14383  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14384 ->
                    (log cfg
                       (fun uu____14387  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14391  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14408 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14408
                         | FStar_Util.Inr c ->
                             let uu____14416 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14416
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14429 =
                               let uu____14430 =
                                 let uu____14457 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14457, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14430
                                in
                             mk uu____14429 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14476 ->
                           let uu____14477 =
                             let uu____14478 =
                               let uu____14479 =
                                 let uu____14506 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14506, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14479
                                in
                             mk uu____14478 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14477))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____14616 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14616 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___150_14636 = cfg  in
                               let uu____14637 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___150_14636.steps);
                                 tcenv = uu____14637;
                                 debug = (uu___150_14636.debug);
                                 delta_level = (uu___150_14636.delta_level);
                                 primitive_steps =
                                   (uu___150_14636.primitive_steps);
                                 strong = (uu___150_14636.strong);
                                 memoize_lazy = (uu___150_14636.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14636.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14642 =
                                 let uu____14643 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14643  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14642
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___151_14646 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___151_14646.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___151_14646.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             }))
                  in
               let uu____14647 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14647
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14658,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14659;
                               FStar_Syntax_Syntax.lbunivs = uu____14660;
                               FStar_Syntax_Syntax.lbtyp = uu____14661;
                               FStar_Syntax_Syntax.lbeff = uu____14662;
                               FStar_Syntax_Syntax.lbdef = uu____14663;_}::uu____14664),uu____14665)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               if
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
               then
                 let binder =
                   let uu____14702 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14702  in
                 let env1 =
                   let uu____14712 =
                     let uu____14719 =
                       let uu____14720 =
                         let uu____14751 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14751,
                           false)
                          in
                       Clos uu____14720  in
                     ((FStar_Pervasives_Native.Some binder), uu____14719)  in
                   uu____14712 :: env  in
                 (log cfg
                    (fun uu____14844  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14848  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14849 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14849))
                 else
                   (let uu____14851 =
                      let uu____14856 =
                        let uu____14857 =
                          let uu____14858 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14858
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14857]  in
                      FStar_Syntax_Subst.open_term uu____14856 body  in
                    match uu____14851 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14867  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14875 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14875  in
                            FStar_Util.Inl
                              (let uu___152_14885 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___152_14885.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___152_14885.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14888  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___153_14890 = lb  in
                             let uu____14891 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___153_14890.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___153_14890.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14891
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14926  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___154_14949 = cfg  in
                             {
                               steps = (uu___154_14949.steps);
                               tcenv = (uu___154_14949.tcenv);
                               debug = (uu___154_14949.debug);
                               delta_level = (uu___154_14949.delta_level);
                               primitive_steps =
                                 (uu___154_14949.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___154_14949.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_14949.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14952  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.steps).compress_uvars ||
                 ((Prims.op_Negation (cfg.steps).zeta) &&
                    (cfg.steps).pure_subterms_within_computations)
               ->
               let uu____14969 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14969 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15005 =
                               let uu___155_15006 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_15006.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_15006.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15005  in
                           let uu____15007 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15007 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15033 =
                                   FStar_List.map (fun uu____15049  -> dummy)
                                     lbs1
                                    in
                                 let uu____15050 =
                                   let uu____15059 =
                                     FStar_List.map
                                       (fun uu____15079  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15059 env  in
                                 FStar_List.append uu____15033 uu____15050
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15103 =
                                       let uu___156_15104 = rc  in
                                       let uu____15105 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___156_15104.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15105;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___156_15104.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15103
                                 | uu____15112 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___157_15116 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___157_15116.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___157_15116.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
                      let uu____15126 =
                        FStar_List.map (fun uu____15142  -> dummy) lbs2  in
                      FStar_List.append uu____15126 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15150 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15150 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___158_15166 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___158_15166.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___158_15166.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15193 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15193
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15212 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15288  ->
                        match uu____15288 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___159_15409 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___159_15409.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___159_15409.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____15212 with
                | (rec_env,memos,uu____15622) ->
                    let uu____15675 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____15986 =
                               let uu____15993 =
                                 let uu____15994 =
                                   let uu____16025 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16025, false)
                                    in
                                 Clos uu____15994  in
                               (FStar_Pervasives_Native.None, uu____15993)
                                in
                             uu____15986 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16135  ->
                     let uu____16136 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16136);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16158 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16160::uu____16161 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16166) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16167 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____16198 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16212 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16212
                              | uu____16223 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16227 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16253 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16271 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16288 =
                        let uu____16289 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16290 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16289 uu____16290
                         in
                      failwith uu____16288
                    else rebuild cfg env stack t2
                | uu____16292 -> norm cfg env stack t2))

and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____16301 = FStar_Syntax_Syntax.range_of_fv f  in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16301  in
            let uu____16302 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            match uu____16302 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16315  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16326  ->
                      let uu____16327 = FStar_Syntax_Print.term_to_string t0
                         in
                      let uu____16328 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16327
                        uu____16328);
                 (let t1 =
                    if
                      ((cfg.steps).unfold_until =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Delta_constant))
                        && (Prims.op_Negation (cfg.steps).unfold_tac)
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t
                     in
                  let n1 = FStar_List.length us  in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack with
                    | (UnivArgs (us',uu____16341))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env)
                           in
                        norm cfg env1 stack1 t1
                    | uu____16396 when (cfg.steps).erase_universes ->
                        norm cfg env stack t1
                    | uu____16399 ->
                        let uu____16402 =
                          let uu____16403 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16403
                           in
                        failwith uu____16402
                  else norm cfg env stack t1))

and (reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                if (cfg.steps).pure_subterms_within_computations
                then
                  let uu___160_16424 = cfg  in
                  let uu____16425 =
                    to_fsteps
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps]
                     in
                  {
                    steps = uu____16425;
                    tcenv = (uu___160_16424.tcenv);
                    debug = (uu___160_16424.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___160_16424.primitive_steps);
                    strong = (uu___160_16424.strong);
                    memoize_lazy = (uu___160_16424.memoize_lazy);
                    normalize_pure_lets =
                      (uu___160_16424.normalize_pure_lets)
                  }
                else
                  (let uu___161_16427 = cfg  in
                   {
                     steps =
                       (let uu___162_16430 = cfg.steps  in
                        {
                          beta = (uu___162_16430.beta);
                          iota = (uu___162_16430.iota);
                          zeta = false;
                          weak = (uu___162_16430.weak);
                          hnf = (uu___162_16430.hnf);
                          primops = (uu___162_16430.primops);
                          eager_unfolding = (uu___162_16430.eager_unfolding);
                          inlining = (uu___162_16430.inlining);
                          no_delta_steps = (uu___162_16430.no_delta_steps);
                          unfold_until = (uu___162_16430.unfold_until);
                          unfold_only = (uu___162_16430.unfold_only);
                          unfold_attr = (uu___162_16430.unfold_attr);
                          unfold_tac = (uu___162_16430.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___162_16430.pure_subterms_within_computations);
                          simplify = (uu___162_16430.simplify);
                          erase_universes = (uu___162_16430.erase_universes);
                          allow_unbound_universes =
                            (uu___162_16430.allow_unbound_universes);
                          reify_ = (uu___162_16430.reify_);
                          compress_uvars = (uu___162_16430.compress_uvars);
                          no_full_norm = (uu___162_16430.no_full_norm);
                          check_no_uvars = (uu___162_16430.check_no_uvars);
                          unmeta = (uu___162_16430.unmeta);
                          unascribe = (uu___162_16430.unascribe)
                        });
                     tcenv = (uu___161_16427.tcenv);
                     debug = (uu___161_16427.debug);
                     delta_level = (uu___161_16427.delta_level);
                     primitive_steps = (uu___161_16427.primitive_steps);
                     strong = (uu___161_16427.strong);
                     memoize_lazy = (uu___161_16427.memoize_lazy);
                     normalize_pure_lets =
                       (uu___161_16427.normalize_pure_lets)
                   })
                 in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head0 = head1  in
                let head2 = FStar_Syntax_Util.unascribe head1  in
                log cfg
                  (fun uu____16460  ->
                     let uu____16461 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16462 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16461
                       uu____16462);
                (let uu____16463 =
                   let uu____16464 = FStar_Syntax_Subst.compress head2  in
                   uu____16464.FStar_Syntax_Syntax.n  in
                 match uu____16463 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16482 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16482 with
                      | (uu____16483,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16489 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16497 =
                                   let uu____16498 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16498.FStar_Syntax_Syntax.n  in
                                 match uu____16497 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16504,uu____16505))
                                     ->
                                     let uu____16514 =
                                       let uu____16515 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16515.FStar_Syntax_Syntax.n  in
                                     (match uu____16514 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16521,msrc,uu____16523))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16532 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16532
                                      | uu____16533 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16534 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16535 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16535 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___163_16540 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___163_16540.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___163_16540.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___163_16540.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      }  in
                                    let uu____16541 = FStar_List.tl stack  in
                                    let uu____16542 =
                                      let uu____16543 =
                                        let uu____16546 =
                                          let uu____16547 =
                                            let uu____16560 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16560)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16547
                                           in
                                        FStar_Syntax_Syntax.mk uu____16546
                                         in
                                      uu____16543
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16541 uu____16542
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16576 =
                                      let uu____16577 = is_return body  in
                                      match uu____16577 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16581;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16582;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16587 -> false  in
                                    if uu____16576
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos  in
                                       let head3 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef
                                          in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body
                                          in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         }  in
                                       let body2 =
                                         let uu____16610 =
                                           let uu____16613 =
                                             let uu____16614 =
                                               let uu____16631 =
                                                 let uu____16634 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16634]  in
                                               (uu____16631, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16614
                                              in
                                           FStar_Syntax_Syntax.mk uu____16613
                                            in
                                         uu____16610
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16650 =
                                           let uu____16651 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16651.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16650 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16657::uu____16658::[])
                                             ->
                                             let uu____16665 =
                                               let uu____16668 =
                                                 let uu____16669 =
                                                   let uu____16676 =
                                                     let uu____16679 =
                                                       let uu____16680 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16680
                                                        in
                                                     let uu____16681 =
                                                       let uu____16684 =
                                                         let uu____16685 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16685
                                                          in
                                                       [uu____16684]  in
                                                     uu____16679 ::
                                                       uu____16681
                                                      in
                                                   (bind1, uu____16676)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16669
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16668
                                                in
                                             uu____16665
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16693 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____16699 =
                                           let uu____16702 =
                                             let uu____16703 =
                                               let uu____16718 =
                                                 let uu____16721 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16722 =
                                                   let uu____16725 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____16726 =
                                                     let uu____16729 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16730 =
                                                       let uu____16733 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____16734 =
                                                         let uu____16737 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16738 =
                                                           let uu____16741 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16741]  in
                                                         uu____16737 ::
                                                           uu____16738
                                                          in
                                                       uu____16733 ::
                                                         uu____16734
                                                        in
                                                     uu____16729 ::
                                                       uu____16730
                                                      in
                                                   uu____16725 :: uu____16726
                                                    in
                                                 uu____16721 :: uu____16722
                                                  in
                                               (bind_inst, uu____16718)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16703
                                              in
                                           FStar_Syntax_Syntax.mk uu____16702
                                            in
                                         uu____16699
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16753  ->
                                            let uu____16754 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16755 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16754 uu____16755);
                                       (let uu____16756 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16756 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16780 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16780 with
                      | (uu____16781,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16816 =
                                  let uu____16817 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16817.FStar_Syntax_Syntax.n  in
                                match uu____16816 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16823) -> t2
                                | uu____16828 -> head3  in
                              let uu____16829 =
                                let uu____16830 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16830.FStar_Syntax_Syntax.n  in
                              match uu____16829 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16836 -> FStar_Pervasives_Native.None
                               in
                            let uu____16837 = maybe_extract_fv head3  in
                            match uu____16837 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16847 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16847
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____16852 = maybe_extract_fv head4
                                     in
                                  match uu____16852 with
                                  | FStar_Pervasives_Native.Some uu____16857
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16858 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____16863 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16878 =
                              match uu____16878 with
                              | (e,q) ->
                                  let uu____16885 =
                                    let uu____16886 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16886.FStar_Syntax_Syntax.n  in
                                  (match uu____16885 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____16901 -> false)
                               in
                            let uu____16902 =
                              let uu____16903 =
                                let uu____16910 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16910 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16903
                               in
                            if uu____16902
                            then
                              let uu____16915 =
                                let uu____16916 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16916
                                 in
                              failwith uu____16915
                            else ());
                           (let uu____16918 = maybe_unfold_action head_app
                               in
                            match uu____16918 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos
                                   in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args))
                                   in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body
                                   in
                                (log cfg
                                   (fun uu____16959  ->
                                      let uu____16960 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16961 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16960 uu____16961);
                                 (let uu____16962 = FStar_List.tl stack  in
                                  norm cfg env uu____16962 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16964) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16988 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16988  in
                     (log cfg
                        (fun uu____16992  ->
                           let uu____16993 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16993);
                      (let uu____16994 = FStar_List.tl stack  in
                       norm cfg env uu____16994 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____16996) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17121  ->
                               match uu____17121 with
                               | (pat,wopt,tm) ->
                                   let uu____17169 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17169)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____17201 = FStar_List.tl stack  in
                     norm cfg env uu____17201 tm
                 | uu____17202 -> fallback ())

and (reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv  in
            log cfg
              (fun uu____17216  ->
                 let uu____17217 = FStar_Ident.string_of_lid msrc  in
                 let uu____17218 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17219 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17217
                   uu____17218 uu____17219);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____17221 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17221 with
               | (uu____17222,return_repr) ->
                   let return_inst =
                     let uu____17231 =
                       let uu____17232 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17232.FStar_Syntax_Syntax.n  in
                     match uu____17231 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17238::[]) ->
                         let uu____17245 =
                           let uu____17248 =
                             let uu____17249 =
                               let uu____17256 =
                                 let uu____17259 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17259]  in
                               (return_tm, uu____17256)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17249  in
                           FStar_Syntax_Syntax.mk uu____17248  in
                         uu____17245 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17267 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17270 =
                     let uu____17273 =
                       let uu____17274 =
                         let uu____17289 =
                           let uu____17292 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17293 =
                             let uu____17296 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17296]  in
                           uu____17292 :: uu____17293  in
                         (return_inst, uu____17289)  in
                       FStar_Syntax_Syntax.Tm_app uu____17274  in
                     FStar_Syntax_Syntax.mk uu____17273  in
                   uu____17270 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17305 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17305 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17308 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17308
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17309;
                     FStar_TypeChecker_Env.mtarget = uu____17310;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17311;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17326 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17326
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17327;
                     FStar_TypeChecker_Env.mtarget = uu____17328;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17329;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17353 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17354 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17353 t FStar_Syntax_Syntax.tun uu____17354)

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____17410  ->
                   match uu____17410 with
                   | (a,imp) ->
                       let uu____17421 = norm cfg env [] a  in
                       (uu____17421, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___164_17435 = comp  in
            let uu____17436 =
              let uu____17437 =
                let uu____17446 = norm cfg env [] t  in
                let uu____17447 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17446, uu____17447)  in
              FStar_Syntax_Syntax.Total uu____17437  in
            {
              FStar_Syntax_Syntax.n = uu____17436;
              FStar_Syntax_Syntax.pos =
                (uu___164_17435.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___164_17435.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___165_17462 = comp  in
            let uu____17463 =
              let uu____17464 =
                let uu____17473 = norm cfg env [] t  in
                let uu____17474 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17473, uu____17474)  in
              FStar_Syntax_Syntax.GTotal uu____17464  in
            {
              FStar_Syntax_Syntax.n = uu____17463;
              FStar_Syntax_Syntax.pos =
                (uu___165_17462.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_17462.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____17526  ->
                      match uu____17526 with
                      | (a,i) ->
                          let uu____17537 = norm cfg env [] a  in
                          (uu____17537, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___83_17548  ->
                      match uu___83_17548 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17552 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____17552
                      | f -> f))
               in
            let uu___166_17556 = comp  in
            let uu____17557 =
              let uu____17558 =
                let uu___167_17559 = ct  in
                let uu____17560 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____17561 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____17564 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____17560;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___167_17559.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____17561;
                  FStar_Syntax_Syntax.effect_args = uu____17564;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____17558  in
            {
              FStar_Syntax_Syntax.n = uu____17557;
              FStar_Syntax_Syntax.pos =
                (uu___166_17556.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_17556.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17575  ->
        match uu____17575 with
        | (x,imp) ->
            let uu____17578 =
              let uu___168_17579 = x  in
              let uu____17580 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___168_17579.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___168_17579.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17580
              }  in
            (uu____17578, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17586 =
          FStar_List.fold_left
            (fun uu____17604  ->
               fun b  ->
                 match uu____17604 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17586 with | (nbs,uu____17644) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____17660 =
              let uu___169_17661 = rc  in
              let uu____17662 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___169_17661.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17662;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___169_17661.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17660
        | uu____17669 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17682  ->
               let uu____17683 = FStar_Syntax_Print.tag_of_term t  in
               let uu____17684 = FStar_Syntax_Print.term_to_string t  in
               let uu____17685 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____17692 =
                 let uu____17693 =
                   let uu____17696 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17696
                    in
                 stack_to_string uu____17693  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____17683 uu____17684 uu____17685 uu____17692);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____17727 =
                     let uu____17728 =
                       let uu____17729 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____17729  in
                     FStar_Util.string_of_int uu____17728  in
                   let uu____17734 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____17735 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17727 uu____17734 uu____17735)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____17789  ->
                     let uu____17790 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17790);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs  in
               let lopt1 = norm_lcomp_opt cfg env'' lopt  in
               let uu____17826 =
                 let uu___170_17827 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___170_17827.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___170_17827.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____17826
           | (Arg (Univ uu____17828,uu____17829,uu____17830))::uu____17831 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17834,uu____17835))::uu____17836 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____17852),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17905  ->
                     let uu____17906 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17906);
                if Prims.op_Negation (cfg.steps).iota
                then
                  (if (cfg.steps).hnf
                   then
                     let arg = closure_as_term cfg env_arg tm  in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____17916 = FStar_ST.op_Bang m  in
                   match uu____17916 with
                   | FStar_Pervasives_Native.None  ->
                       if (cfg.steps).hnf
                       then
                         let arg = closure_as_term cfg env_arg tm  in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r
                            in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____18053,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____18100 =
                 log cfg
                   (fun uu____18104  ->
                      let uu____18105 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18105);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____18109 =
                 let uu____18110 = FStar_Syntax_Subst.compress t1  in
                 uu____18110.FStar_Syntax_Syntax.n  in
               (match uu____18109 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18137 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____18137  in
                    (log cfg
                       (fun uu____18141  ->
                          let uu____18142 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18142);
                     (let uu____18143 = FStar_List.tl stack  in
                      norm cfg env1 uu____18143 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18144);
                       FStar_Syntax_Syntax.pos = uu____18145;
                       FStar_Syntax_Syntax.vars = uu____18146;_},(e,uu____18148)::[])
                    -> norm cfg env1 stack' e
                | uu____18177 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18197  ->
                     let uu____18198 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18198);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____18203 =
                   log cfg
                     (fun uu____18208  ->
                        let uu____18209 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____18210 =
                          let uu____18211 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18228  ->
                                    match uu____18228 with
                                    | (p,uu____18238,uu____18239) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____18211
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18209 uu____18210);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___84_18256  ->
                                match uu___84_18256 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18257 -> false))
                         in
                      let uu___171_18258 = cfg  in
                      {
                        steps =
                          (let uu___172_18261 = cfg.steps  in
                           {
                             beta = (uu___172_18261.beta);
                             iota = (uu___172_18261.iota);
                             zeta = false;
                             weak = (uu___172_18261.weak);
                             hnf = (uu___172_18261.hnf);
                             primops = (uu___172_18261.primops);
                             eager_unfolding =
                               (uu___172_18261.eager_unfolding);
                             inlining = (uu___172_18261.inlining);
                             no_delta_steps = (uu___172_18261.no_delta_steps);
                             unfold_until = (uu___172_18261.unfold_until);
                             unfold_only = (uu___172_18261.unfold_only);
                             unfold_attr = (uu___172_18261.unfold_attr);
                             unfold_tac = (uu___172_18261.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___172_18261.pure_subterms_within_computations);
                             simplify = (uu___172_18261.simplify);
                             erase_universes =
                               (uu___172_18261.erase_universes);
                             allow_unbound_universes =
                               (uu___172_18261.allow_unbound_universes);
                             reify_ = (uu___172_18261.reify_);
                             compress_uvars = (uu___172_18261.compress_uvars);
                             no_full_norm = (uu___172_18261.no_full_norm);
                             check_no_uvars = (uu___172_18261.check_no_uvars);
                             unmeta = (uu___172_18261.unmeta);
                             unascribe = (uu___172_18261.unascribe)
                           });
                        tcenv = (uu___171_18258.tcenv);
                        debug = (uu___171_18258.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___171_18258.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___171_18258.memoize_lazy);
                        normalize_pure_lets =
                          (uu___171_18258.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18293 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18314 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18374  ->
                                    fun uu____18375  ->
                                      match (uu____18374, uu____18375) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18466 = norm_pat env3 p1
                                             in
                                          (match uu____18466 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____18314 with
                           | (pats1,env3) ->
                               ((let uu___173_18548 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___173_18548.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___174_18567 = x  in
                            let uu____18568 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___174_18567.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___174_18567.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18568
                            }  in
                          ((let uu___175_18582 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___175_18582.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___176_18593 = x  in
                            let uu____18594 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___176_18593.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___176_18593.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18594
                            }  in
                          ((let uu___177_18608 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___177_18608.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___178_18624 = x  in
                            let uu____18625 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_18624.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_18624.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18625
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___179_18632 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___179_18632.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18642 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18656 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____18656 with
                                  | (p,wopt,e) ->
                                      let uu____18676 = norm_pat env1 p  in
                                      (match uu____18676 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18701 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18701
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____18707 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____18707)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18717) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18722 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18723;
                         FStar_Syntax_Syntax.fv_delta = uu____18724;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18725;
                         FStar_Syntax_Syntax.fv_delta = uu____18726;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18727);_}
                       -> true
                   | uu____18734 -> false  in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b  in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r
                          in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch
                    in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                      in
                   let uu____18879 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____18879 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18966 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19005 ->
                                 let uu____19006 =
                                   let uu____19007 = is_cons head1  in
                                   Prims.op_Negation uu____19007  in
                                 FStar_Util.Inr uu____19006)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19032 =
                              let uu____19033 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____19033.FStar_Syntax_Syntax.n  in
                            (match uu____19032 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19051 ->
                                 let uu____19052 =
                                   let uu____19053 = is_cons head1  in
                                   Prims.op_Negation uu____19053  in
                                 FStar_Util.Inr uu____19052))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19122)::rest_a,(p1,uu____19125)::rest_p) ->
                       let uu____19169 = matches_pat t2 p1  in
                       (match uu____19169 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19218 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19324 = matches_pat scrutinee1 p1  in
                       (match uu____19324 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19364  ->
                                  let uu____19365 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____19366 =
                                    let uu____19367 =
                                      FStar_List.map
                                        (fun uu____19377  ->
                                           match uu____19377 with
                                           | (uu____19382,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____19367
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19365 uu____19366);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19413  ->
                                       match uu____19413 with
                                       | (bv,t2) ->
                                           let uu____19436 =
                                             let uu____19443 =
                                               let uu____19446 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____19446
                                                in
                                             let uu____19447 =
                                               let uu____19448 =
                                                 let uu____19479 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____19479, false)
                                                  in
                                               Clos uu____19448  in
                                             (uu____19443, uu____19447)  in
                                           uu____19436 :: env2) env1 s
                                 in
                              let uu____19596 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____19596)))
                    in
                 if Prims.op_Negation (cfg.steps).iota
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___85_19617  ->
                match uu___85_19617 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19621 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19627 -> d  in
      let uu____19630 = to_fsteps s  in
      let uu____19631 =
        let uu____19632 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
        let uu____19633 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
        let uu____19634 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
        let uu____19635 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
           in
        let uu____19636 =
          FStar_TypeChecker_Env.debug e
            (FStar_Options.Other "print_normalized_terms")
           in
        {
          gen = uu____19632;
          primop = uu____19633;
          b380 = uu____19634;
          norm_delayed = uu____19635;
          print_normalized = uu____19636
        }  in
      let uu____19637 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____19639 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations)
              in
           Prims.op_Negation uu____19639)
         in
      {
        steps = uu____19630;
        tcenv = e;
        debug = uu____19631;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____19637
      }
  
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e  in
          let c1 =
            let uu___180_19664 = config s e  in
            {
              steps = (uu___180_19664.steps);
              tcenv = (uu___180_19664.tcenv);
              debug = (uu___180_19664.debug);
              delta_level = (uu___180_19664.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___180_19664.strong);
              memoize_lazy = (uu___180_19664.memoize_lazy);
              normalize_pure_lets = (uu___180_19664.normalize_pure_lets)
            }  in
          norm c1 [] [] t
  
let (normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____19689 = config s e  in norm_comp uu____19689 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____19702 = config [] env  in norm_universe uu____19702 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____19720 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19720  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____19727 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___181_19746 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___181_19746.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___181_19746.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____19753 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____19753
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___182_19762 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___182_19762.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___182_19762.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___182_19762.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___183_19764 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___183_19764.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___183_19764.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___183_19764.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___183_19764.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___184_19765 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___184_19765.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___184_19765.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____19767 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____19779 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19779  in
      let uu____19786 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____19786
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____19790  ->
                 let uu____19791 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____19791)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____19808 =
                let uu____19813 =
                  let uu____19814 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19814
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19813)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____19808);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19825 = config [AllowUnboundUniverses] env  in
          norm_comp uu____19825 [] c
        with
        | e ->
            ((let uu____19838 =
                let uu____19843 =
                  let uu____19844 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19844
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19843)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____19838);
             c)
         in
      FStar_Syntax_Print.comp_to_string c1
  
let (normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0  in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____19881 =
                     let uu____19882 =
                       let uu____19889 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____19889)  in
                     FStar_Syntax_Syntax.Tm_refine uu____19882  in
                   mk uu____19881 t01.FStar_Syntax_Syntax.pos
               | uu____19894 -> t2)
          | uu____19895 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
  
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____19935 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____19935 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19964 ->
                 let uu____19971 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____19971 with
                  | (actuals,uu____19981,uu____19982) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19996 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____19996 with
                         | (binders,args) ->
                             let uu____20013 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____20013
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____20021 ->
          let uu____20022 = FStar_Syntax_Util.head_and_args t  in
          (match uu____20022 with
           | (head1,args) ->
               let uu____20059 =
                 let uu____20060 = FStar_Syntax_Subst.compress head1  in
                 uu____20060.FStar_Syntax_Syntax.n  in
               (match uu____20059 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20063,thead) ->
                    let uu____20089 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____20089 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20131 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___189_20139 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___189_20139.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___189_20139.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___189_20139.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___189_20139.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___189_20139.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___189_20139.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___189_20139.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___189_20139.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___189_20139.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___189_20139.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___189_20139.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___189_20139.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___189_20139.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___189_20139.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___189_20139.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___189_20139.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___189_20139.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___189_20139.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___189_20139.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___189_20139.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___189_20139.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___189_20139.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___189_20139.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___189_20139.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___189_20139.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___189_20139.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___189_20139.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___189_20139.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___189_20139.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___189_20139.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___189_20139.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___189_20139.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____20131 with
                            | (uu____20140,ty,uu____20142) ->
                                eta_expand_with_type env t ty))
                | uu____20143 ->
                    let uu____20144 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___190_20152 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___190_20152.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___190_20152.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___190_20152.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___190_20152.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___190_20152.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___190_20152.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___190_20152.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___190_20152.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___190_20152.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___190_20152.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___190_20152.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___190_20152.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___190_20152.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___190_20152.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___190_20152.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___190_20152.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___190_20152.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___190_20152.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___190_20152.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___190_20152.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___190_20152.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___190_20152.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___190_20152.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___190_20152.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___190_20152.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___190_20152.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___190_20152.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___190_20152.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___190_20152.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___190_20152.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___190_20152.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___190_20152.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____20144 with
                     | (uu____20153,ty,uu____20155) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___191_20212 = x  in
      let uu____20213 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___191_20212.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___191_20212.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20213
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20216 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20241 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20242 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20243 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20244 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20251 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20252 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___192_20280 = rc  in
          let uu____20281 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____20288 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___192_20280.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20281;
            FStar_Syntax_Syntax.residual_flags = uu____20288
          }  in
        let uu____20291 =
          let uu____20292 =
            let uu____20309 = elim_delayed_subst_binders bs  in
            let uu____20316 = elim_delayed_subst_term t2  in
            let uu____20317 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____20309, uu____20316, uu____20317)  in
          FStar_Syntax_Syntax.Tm_abs uu____20292  in
        mk1 uu____20291
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____20346 =
          let uu____20347 =
            let uu____20360 = elim_delayed_subst_binders bs  in
            let uu____20367 = elim_delayed_subst_comp c  in
            (uu____20360, uu____20367)  in
          FStar_Syntax_Syntax.Tm_arrow uu____20347  in
        mk1 uu____20346
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____20380 =
          let uu____20381 =
            let uu____20388 = elim_bv bv  in
            let uu____20389 = elim_delayed_subst_term phi  in
            (uu____20388, uu____20389)  in
          FStar_Syntax_Syntax.Tm_refine uu____20381  in
        mk1 uu____20380
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____20412 =
          let uu____20413 =
            let uu____20428 = elim_delayed_subst_term t2  in
            let uu____20429 = elim_delayed_subst_args args  in
            (uu____20428, uu____20429)  in
          FStar_Syntax_Syntax.Tm_app uu____20413  in
        mk1 uu____20412
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___193_20493 = p  in
              let uu____20494 =
                let uu____20495 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____20495  in
              {
                FStar_Syntax_Syntax.v = uu____20494;
                FStar_Syntax_Syntax.p =
                  (uu___193_20493.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___194_20497 = p  in
              let uu____20498 =
                let uu____20499 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____20499  in
              {
                FStar_Syntax_Syntax.v = uu____20498;
                FStar_Syntax_Syntax.p =
                  (uu___194_20497.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___195_20506 = p  in
              let uu____20507 =
                let uu____20508 =
                  let uu____20515 = elim_bv x  in
                  let uu____20516 = elim_delayed_subst_term t0  in
                  (uu____20515, uu____20516)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____20508  in
              {
                FStar_Syntax_Syntax.v = uu____20507;
                FStar_Syntax_Syntax.p =
                  (uu___195_20506.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___196_20535 = p  in
              let uu____20536 =
                let uu____20537 =
                  let uu____20550 =
                    FStar_List.map
                      (fun uu____20573  ->
                         match uu____20573 with
                         | (x,b) ->
                             let uu____20586 = elim_pat x  in
                             (uu____20586, b)) pats
                     in
                  (fv, uu____20550)  in
                FStar_Syntax_Syntax.Pat_cons uu____20537  in
              {
                FStar_Syntax_Syntax.v = uu____20536;
                FStar_Syntax_Syntax.p =
                  (uu___196_20535.FStar_Syntax_Syntax.p)
              }
          | uu____20599 -> p  in
        let elim_branch uu____20621 =
          match uu____20621 with
          | (pat,wopt,t3) ->
              let uu____20647 = elim_pat pat  in
              let uu____20650 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____20653 = elim_delayed_subst_term t3  in
              (uu____20647, uu____20650, uu____20653)
           in
        let uu____20658 =
          let uu____20659 =
            let uu____20682 = elim_delayed_subst_term t2  in
            let uu____20683 = FStar_List.map elim_branch branches  in
            (uu____20682, uu____20683)  in
          FStar_Syntax_Syntax.Tm_match uu____20659  in
        mk1 uu____20658
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____20792 =
          match uu____20792 with
          | (tc,topt) ->
              let uu____20827 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____20837 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____20837
                | FStar_Util.Inr c ->
                    let uu____20839 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____20839
                 in
              let uu____20840 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____20827, uu____20840)
           in
        let uu____20849 =
          let uu____20850 =
            let uu____20877 = elim_delayed_subst_term t2  in
            let uu____20878 = elim_ascription a  in
            (uu____20877, uu____20878, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____20850  in
        mk1 uu____20849
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___197_20923 = lb  in
          let uu____20924 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____20927 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___197_20923.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___197_20923.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____20924;
            FStar_Syntax_Syntax.lbeff =
              (uu___197_20923.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____20927
          }  in
        let uu____20930 =
          let uu____20931 =
            let uu____20944 =
              let uu____20951 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____20951)  in
            let uu____20960 = elim_delayed_subst_term t2  in
            (uu____20944, uu____20960)  in
          FStar_Syntax_Syntax.Tm_let uu____20931  in
        mk1 uu____20930
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____20993 =
          let uu____20994 =
            let uu____21011 = elim_delayed_subst_term t2  in
            (uv, uu____21011)  in
          FStar_Syntax_Syntax.Tm_uvar uu____20994  in
        mk1 uu____20993
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21028 =
          let uu____21029 =
            let uu____21036 = elim_delayed_subst_term t2  in
            let uu____21037 = elim_delayed_subst_meta md  in
            (uu____21036, uu____21037)  in
          FStar_Syntax_Syntax.Tm_meta uu____21029  in
        mk1 uu____21028

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___86_21044  ->
         match uu___86_21044 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21048 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____21048
         | f -> f) flags1

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____21069 =
          let uu____21070 =
            let uu____21079 = elim_delayed_subst_term t  in
            (uu____21079, uopt)  in
          FStar_Syntax_Syntax.Total uu____21070  in
        mk1 uu____21069
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21092 =
          let uu____21093 =
            let uu____21102 = elim_delayed_subst_term t  in
            (uu____21102, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____21093  in
        mk1 uu____21092
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___198_21107 = ct  in
          let uu____21108 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____21111 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____21120 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___198_21107.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___198_21107.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21108;
            FStar_Syntax_Syntax.effect_args = uu____21111;
            FStar_Syntax_Syntax.flags = uu____21120
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___87_21123  ->
    match uu___87_21123 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21135 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____21135
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21168 =
          let uu____21175 = elim_delayed_subst_term t  in (m, uu____21175)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____21168
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21183 =
          let uu____21192 = elim_delayed_subst_term t  in
          (m1, m2, uu____21192)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21183
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21200 =
          let uu____21209 = elim_delayed_subst_term t  in (d, s, uu____21209)
           in
        FStar_Syntax_Syntax.Meta_alien uu____21200
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____21232  ->
         match uu____21232 with
         | (t,q) ->
             let uu____21243 = elim_delayed_subst_term t  in (uu____21243, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21263  ->
         match uu____21263 with
         | (x,q) ->
             let uu____21274 =
               let uu___199_21275 = x  in
               let uu____21276 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___199_21275.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___199_21275.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21276
               }  in
             (uu____21274, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____21352,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____21358,FStar_Util.Inl t) ->
                let uu____21364 =
                  let uu____21367 =
                    let uu____21368 =
                      let uu____21381 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____21381)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____21368  in
                  FStar_Syntax_Syntax.mk uu____21367  in
                uu____21364 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____21385 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____21385 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____21413 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____21468 ->
                    let uu____21469 =
                      let uu____21478 =
                        let uu____21479 = FStar_Syntax_Subst.compress t4  in
                        uu____21479.FStar_Syntax_Syntax.n  in
                      (uu____21478, tc)  in
                    (match uu____21469 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____21504) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____21541) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____21580,FStar_Util.Inl uu____21581) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____21604 -> failwith "Impossible")
                 in
              (match uu____21413 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____21709 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____21709 with
          | (univ_names1,binders1,tc) ->
              let uu____21767 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____21767)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____21802 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____21802 with
          | (univ_names1,binders1,tc) ->
              let uu____21862 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____21862)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____21895 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____21895 with
           | (univ_names1,binders1,typ1) ->
               let uu___200_21923 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___200_21923.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___200_21923.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___200_21923.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___200_21923.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___201_21944 = s  in
          let uu____21945 =
            let uu____21946 =
              let uu____21955 = FStar_List.map (elim_uvars env) sigs  in
              (uu____21955, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____21946  in
          {
            FStar_Syntax_Syntax.sigel = uu____21945;
            FStar_Syntax_Syntax.sigrng =
              (uu___201_21944.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___201_21944.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___201_21944.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___201_21944.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____21972 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____21972 with
           | (univ_names1,uu____21990,typ1) ->
               let uu___202_22004 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_22004.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_22004.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_22004.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_22004.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22010 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22010 with
           | (univ_names1,uu____22028,typ1) ->
               let uu___203_22042 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_22042.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_22042.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_22042.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___203_22042.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22076 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____22076 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22099 =
                            let uu____22100 =
                              let uu____22101 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____22101  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22100
                             in
                          elim_delayed_subst_term uu____22099  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___204_22104 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___204_22104.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___204_22104.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___205_22105 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___205_22105.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___205_22105.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___205_22105.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___205_22105.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___206_22117 = s  in
          let uu____22118 =
            let uu____22119 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____22119  in
          {
            FStar_Syntax_Syntax.sigel = uu____22118;
            FStar_Syntax_Syntax.sigrng =
              (uu___206_22117.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___206_22117.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___206_22117.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___206_22117.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22123 = elim_uvars_aux_t env us [] t  in
          (match uu____22123 with
           | (us1,uu____22141,t1) ->
               let uu___207_22155 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_22155.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_22155.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_22155.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_22155.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22156 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22158 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____22158 with
           | (univs1,binders,signature) ->
               let uu____22186 =
                 let uu____22195 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____22195 with
                 | (univs_opening,univs2) ->
                     let uu____22222 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____22222)
                  in
               (match uu____22186 with
                | (univs_opening,univs_closing) ->
                    let uu____22239 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____22245 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____22246 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____22245, uu____22246)  in
                    (match uu____22239 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____22268 =
                           match uu____22268 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____22286 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____22286 with
                                | (us1,t1) ->
                                    let uu____22297 =
                                      let uu____22302 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____22309 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____22302, uu____22309)  in
                                    (match uu____22297 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____22322 =
                                           let uu____22327 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____22336 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____22327, uu____22336)  in
                                         (match uu____22322 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____22352 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____22352
                                                 in
                                              let uu____22353 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____22353 with
                                               | (uu____22374,uu____22375,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____22390 =
                                                       let uu____22391 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____22391
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____22390
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____22396 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____22396 with
                           | (uu____22409,uu____22410,t1) -> t1  in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____22470 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____22487 =
                               let uu____22488 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____22488.FStar_Syntax_Syntax.n  in
                             match uu____22487 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____22547 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____22576 =
                               let uu____22577 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____22577.FStar_Syntax_Syntax.n  in
                             match uu____22576 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____22598) ->
                                 let uu____22619 = destruct_action_body body
                                    in
                                 (match uu____22619 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____22664 ->
                                 let uu____22665 = destruct_action_body t  in
                                 (match uu____22665 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____22714 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____22714 with
                           | (action_univs,t) ->
                               let uu____22723 = destruct_action_typ_templ t
                                  in
                               (match uu____22723 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___208_22764 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___208_22764.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___208_22764.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___209_22766 = ed  in
                           let uu____22767 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____22768 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____22769 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____22770 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____22771 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____22772 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____22773 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____22774 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____22775 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____22776 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____22777 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____22778 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____22779 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____22780 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___209_22766.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___209_22766.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____22767;
                             FStar_Syntax_Syntax.bind_wp = uu____22768;
                             FStar_Syntax_Syntax.if_then_else = uu____22769;
                             FStar_Syntax_Syntax.ite_wp = uu____22770;
                             FStar_Syntax_Syntax.stronger = uu____22771;
                             FStar_Syntax_Syntax.close_wp = uu____22772;
                             FStar_Syntax_Syntax.assert_p = uu____22773;
                             FStar_Syntax_Syntax.assume_p = uu____22774;
                             FStar_Syntax_Syntax.null_wp = uu____22775;
                             FStar_Syntax_Syntax.trivial = uu____22776;
                             FStar_Syntax_Syntax.repr = uu____22777;
                             FStar_Syntax_Syntax.return_repr = uu____22778;
                             FStar_Syntax_Syntax.bind_repr = uu____22779;
                             FStar_Syntax_Syntax.actions = uu____22780
                           }  in
                         let uu___210_22783 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___210_22783.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___210_22783.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___210_22783.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___210_22783.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_22800 =
            match uu___88_22800 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____22827 = elim_uvars_aux_t env us [] t  in
                (match uu____22827 with
                 | (us1,uu____22851,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___211_22870 = sub_eff  in
            let uu____22871 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____22874 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___211_22870.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___211_22870.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____22871;
              FStar_Syntax_Syntax.lift = uu____22874
            }  in
          let uu___212_22877 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___212_22877.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_22877.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_22877.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_22877.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____22887 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____22887 with
           | (univ_names1,binders1,comp1) ->
               let uu___213_22921 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_22921.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_22921.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_22921.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_22921.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____22932 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  