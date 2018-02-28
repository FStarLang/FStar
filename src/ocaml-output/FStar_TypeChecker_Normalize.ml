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
let cases :
  'Auu____162 'Auu____163 .
    ('Auu____163 -> 'Auu____162) ->
      'Auu____162 ->
        'Auu____163 FStar_Pervasives_Native.option -> 'Auu____162
  =
  fun f  ->
    fun d  ->
      fun uu___75_180  ->
        match uu___75_180 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
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
  unfold_attr:
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option ;
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
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
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
    let add_opt x uu___76_1161 =
      match uu___76_1161 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
      | FStar_Pervasives_Native.Some xs ->
          FStar_Pervasives_Native.Some (x :: xs)
       in
    let add_one1 s1 fs =
      match s1 with
      | Beta  ->
          let uu___94_1188 = fs  in
          {
            beta = true;
            iota = (uu___94_1188.iota);
            zeta = (uu___94_1188.zeta);
            weak = (uu___94_1188.weak);
            hnf = (uu___94_1188.hnf);
            primops = (uu___94_1188.primops);
            eager_unfolding = (uu___94_1188.eager_unfolding);
            inlining = (uu___94_1188.inlining);
            no_delta_steps = (uu___94_1188.no_delta_steps);
            unfold_until = (uu___94_1188.unfold_until);
            unfold_only = (uu___94_1188.unfold_only);
            unfold_attr = (uu___94_1188.unfold_attr);
            unfold_tac = (uu___94_1188.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1188.pure_subterms_within_computations);
            simplify = (uu___94_1188.simplify);
            erase_universes = (uu___94_1188.erase_universes);
            allow_unbound_universes = (uu___94_1188.allow_unbound_universes);
            reify_ = (uu___94_1188.reify_);
            compress_uvars = (uu___94_1188.compress_uvars);
            no_full_norm = (uu___94_1188.no_full_norm);
            check_no_uvars = (uu___94_1188.check_no_uvars);
            unmeta = (uu___94_1188.unmeta);
            unascribe = (uu___94_1188.unascribe)
          }
      | Iota  ->
          let uu___95_1189 = fs  in
          {
            beta = (uu___95_1189.beta);
            iota = true;
            zeta = (uu___95_1189.zeta);
            weak = (uu___95_1189.weak);
            hnf = (uu___95_1189.hnf);
            primops = (uu___95_1189.primops);
            eager_unfolding = (uu___95_1189.eager_unfolding);
            inlining = (uu___95_1189.inlining);
            no_delta_steps = (uu___95_1189.no_delta_steps);
            unfold_until = (uu___95_1189.unfold_until);
            unfold_only = (uu___95_1189.unfold_only);
            unfold_attr = (uu___95_1189.unfold_attr);
            unfold_tac = (uu___95_1189.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1189.pure_subterms_within_computations);
            simplify = (uu___95_1189.simplify);
            erase_universes = (uu___95_1189.erase_universes);
            allow_unbound_universes = (uu___95_1189.allow_unbound_universes);
            reify_ = (uu___95_1189.reify_);
            compress_uvars = (uu___95_1189.compress_uvars);
            no_full_norm = (uu___95_1189.no_full_norm);
            check_no_uvars = (uu___95_1189.check_no_uvars);
            unmeta = (uu___95_1189.unmeta);
            unascribe = (uu___95_1189.unascribe)
          }
      | Zeta  ->
          let uu___96_1190 = fs  in
          {
            beta = (uu___96_1190.beta);
            iota = (uu___96_1190.iota);
            zeta = true;
            weak = (uu___96_1190.weak);
            hnf = (uu___96_1190.hnf);
            primops = (uu___96_1190.primops);
            eager_unfolding = (uu___96_1190.eager_unfolding);
            inlining = (uu___96_1190.inlining);
            no_delta_steps = (uu___96_1190.no_delta_steps);
            unfold_until = (uu___96_1190.unfold_until);
            unfold_only = (uu___96_1190.unfold_only);
            unfold_attr = (uu___96_1190.unfold_attr);
            unfold_tac = (uu___96_1190.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1190.pure_subterms_within_computations);
            simplify = (uu___96_1190.simplify);
            erase_universes = (uu___96_1190.erase_universes);
            allow_unbound_universes = (uu___96_1190.allow_unbound_universes);
            reify_ = (uu___96_1190.reify_);
            compress_uvars = (uu___96_1190.compress_uvars);
            no_full_norm = (uu___96_1190.no_full_norm);
            check_no_uvars = (uu___96_1190.check_no_uvars);
            unmeta = (uu___96_1190.unmeta);
            unascribe = (uu___96_1190.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___97_1191 = fs  in
          {
            beta = false;
            iota = (uu___97_1191.iota);
            zeta = (uu___97_1191.zeta);
            weak = (uu___97_1191.weak);
            hnf = (uu___97_1191.hnf);
            primops = (uu___97_1191.primops);
            eager_unfolding = (uu___97_1191.eager_unfolding);
            inlining = (uu___97_1191.inlining);
            no_delta_steps = (uu___97_1191.no_delta_steps);
            unfold_until = (uu___97_1191.unfold_until);
            unfold_only = (uu___97_1191.unfold_only);
            unfold_attr = (uu___97_1191.unfold_attr);
            unfold_tac = (uu___97_1191.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1191.pure_subterms_within_computations);
            simplify = (uu___97_1191.simplify);
            erase_universes = (uu___97_1191.erase_universes);
            allow_unbound_universes = (uu___97_1191.allow_unbound_universes);
            reify_ = (uu___97_1191.reify_);
            compress_uvars = (uu___97_1191.compress_uvars);
            no_full_norm = (uu___97_1191.no_full_norm);
            check_no_uvars = (uu___97_1191.check_no_uvars);
            unmeta = (uu___97_1191.unmeta);
            unascribe = (uu___97_1191.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___98_1192 = fs  in
          {
            beta = (uu___98_1192.beta);
            iota = false;
            zeta = (uu___98_1192.zeta);
            weak = (uu___98_1192.weak);
            hnf = (uu___98_1192.hnf);
            primops = (uu___98_1192.primops);
            eager_unfolding = (uu___98_1192.eager_unfolding);
            inlining = (uu___98_1192.inlining);
            no_delta_steps = (uu___98_1192.no_delta_steps);
            unfold_until = (uu___98_1192.unfold_until);
            unfold_only = (uu___98_1192.unfold_only);
            unfold_attr = (uu___98_1192.unfold_attr);
            unfold_tac = (uu___98_1192.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1192.pure_subterms_within_computations);
            simplify = (uu___98_1192.simplify);
            erase_universes = (uu___98_1192.erase_universes);
            allow_unbound_universes = (uu___98_1192.allow_unbound_universes);
            reify_ = (uu___98_1192.reify_);
            compress_uvars = (uu___98_1192.compress_uvars);
            no_full_norm = (uu___98_1192.no_full_norm);
            check_no_uvars = (uu___98_1192.check_no_uvars);
            unmeta = (uu___98_1192.unmeta);
            unascribe = (uu___98_1192.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___99_1193 = fs  in
          {
            beta = (uu___99_1193.beta);
            iota = (uu___99_1193.iota);
            zeta = false;
            weak = (uu___99_1193.weak);
            hnf = (uu___99_1193.hnf);
            primops = (uu___99_1193.primops);
            eager_unfolding = (uu___99_1193.eager_unfolding);
            inlining = (uu___99_1193.inlining);
            no_delta_steps = (uu___99_1193.no_delta_steps);
            unfold_until = (uu___99_1193.unfold_until);
            unfold_only = (uu___99_1193.unfold_only);
            unfold_attr = (uu___99_1193.unfold_attr);
            unfold_tac = (uu___99_1193.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1193.pure_subterms_within_computations);
            simplify = (uu___99_1193.simplify);
            erase_universes = (uu___99_1193.erase_universes);
            allow_unbound_universes = (uu___99_1193.allow_unbound_universes);
            reify_ = (uu___99_1193.reify_);
            compress_uvars = (uu___99_1193.compress_uvars);
            no_full_norm = (uu___99_1193.no_full_norm);
            check_no_uvars = (uu___99_1193.check_no_uvars);
            unmeta = (uu___99_1193.unmeta);
            unascribe = (uu___99_1193.unascribe)
          }
      | Exclude uu____1194 -> failwith "Bad exclude"
      | Weak  ->
          let uu___100_1195 = fs  in
          {
            beta = (uu___100_1195.beta);
            iota = (uu___100_1195.iota);
            zeta = (uu___100_1195.zeta);
            weak = true;
            hnf = (uu___100_1195.hnf);
            primops = (uu___100_1195.primops);
            eager_unfolding = (uu___100_1195.eager_unfolding);
            inlining = (uu___100_1195.inlining);
            no_delta_steps = (uu___100_1195.no_delta_steps);
            unfold_until = (uu___100_1195.unfold_until);
            unfold_only = (uu___100_1195.unfold_only);
            unfold_attr = (uu___100_1195.unfold_attr);
            unfold_tac = (uu___100_1195.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1195.pure_subterms_within_computations);
            simplify = (uu___100_1195.simplify);
            erase_universes = (uu___100_1195.erase_universes);
            allow_unbound_universes = (uu___100_1195.allow_unbound_universes);
            reify_ = (uu___100_1195.reify_);
            compress_uvars = (uu___100_1195.compress_uvars);
            no_full_norm = (uu___100_1195.no_full_norm);
            check_no_uvars = (uu___100_1195.check_no_uvars);
            unmeta = (uu___100_1195.unmeta);
            unascribe = (uu___100_1195.unascribe)
          }
      | HNF  ->
          let uu___101_1196 = fs  in
          {
            beta = (uu___101_1196.beta);
            iota = (uu___101_1196.iota);
            zeta = (uu___101_1196.zeta);
            weak = (uu___101_1196.weak);
            hnf = true;
            primops = (uu___101_1196.primops);
            eager_unfolding = (uu___101_1196.eager_unfolding);
            inlining = (uu___101_1196.inlining);
            no_delta_steps = (uu___101_1196.no_delta_steps);
            unfold_until = (uu___101_1196.unfold_until);
            unfold_only = (uu___101_1196.unfold_only);
            unfold_attr = (uu___101_1196.unfold_attr);
            unfold_tac = (uu___101_1196.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1196.pure_subterms_within_computations);
            simplify = (uu___101_1196.simplify);
            erase_universes = (uu___101_1196.erase_universes);
            allow_unbound_universes = (uu___101_1196.allow_unbound_universes);
            reify_ = (uu___101_1196.reify_);
            compress_uvars = (uu___101_1196.compress_uvars);
            no_full_norm = (uu___101_1196.no_full_norm);
            check_no_uvars = (uu___101_1196.check_no_uvars);
            unmeta = (uu___101_1196.unmeta);
            unascribe = (uu___101_1196.unascribe)
          }
      | Primops  ->
          let uu___102_1197 = fs  in
          {
            beta = (uu___102_1197.beta);
            iota = (uu___102_1197.iota);
            zeta = (uu___102_1197.zeta);
            weak = (uu___102_1197.weak);
            hnf = (uu___102_1197.hnf);
            primops = true;
            eager_unfolding = (uu___102_1197.eager_unfolding);
            inlining = (uu___102_1197.inlining);
            no_delta_steps = (uu___102_1197.no_delta_steps);
            unfold_until = (uu___102_1197.unfold_until);
            unfold_only = (uu___102_1197.unfold_only);
            unfold_attr = (uu___102_1197.unfold_attr);
            unfold_tac = (uu___102_1197.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1197.pure_subterms_within_computations);
            simplify = (uu___102_1197.simplify);
            erase_universes = (uu___102_1197.erase_universes);
            allow_unbound_universes = (uu___102_1197.allow_unbound_universes);
            reify_ = (uu___102_1197.reify_);
            compress_uvars = (uu___102_1197.compress_uvars);
            no_full_norm = (uu___102_1197.no_full_norm);
            check_no_uvars = (uu___102_1197.check_no_uvars);
            unmeta = (uu___102_1197.unmeta);
            unascribe = (uu___102_1197.unascribe)
          }
      | Eager_unfolding  ->
          let uu___103_1198 = fs  in
          {
            beta = (uu___103_1198.beta);
            iota = (uu___103_1198.iota);
            zeta = (uu___103_1198.zeta);
            weak = (uu___103_1198.weak);
            hnf = (uu___103_1198.hnf);
            primops = (uu___103_1198.primops);
            eager_unfolding = true;
            inlining = (uu___103_1198.inlining);
            no_delta_steps = (uu___103_1198.no_delta_steps);
            unfold_until = (uu___103_1198.unfold_until);
            unfold_only = (uu___103_1198.unfold_only);
            unfold_attr = (uu___103_1198.unfold_attr);
            unfold_tac = (uu___103_1198.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1198.pure_subterms_within_computations);
            simplify = (uu___103_1198.simplify);
            erase_universes = (uu___103_1198.erase_universes);
            allow_unbound_universes = (uu___103_1198.allow_unbound_universes);
            reify_ = (uu___103_1198.reify_);
            compress_uvars = (uu___103_1198.compress_uvars);
            no_full_norm = (uu___103_1198.no_full_norm);
            check_no_uvars = (uu___103_1198.check_no_uvars);
            unmeta = (uu___103_1198.unmeta);
            unascribe = (uu___103_1198.unascribe)
          }
      | Inlining  ->
          let uu___104_1199 = fs  in
          {
            beta = (uu___104_1199.beta);
            iota = (uu___104_1199.iota);
            zeta = (uu___104_1199.zeta);
            weak = (uu___104_1199.weak);
            hnf = (uu___104_1199.hnf);
            primops = (uu___104_1199.primops);
            eager_unfolding = (uu___104_1199.eager_unfolding);
            inlining = true;
            no_delta_steps = (uu___104_1199.no_delta_steps);
            unfold_until = (uu___104_1199.unfold_until);
            unfold_only = (uu___104_1199.unfold_only);
            unfold_attr = (uu___104_1199.unfold_attr);
            unfold_tac = (uu___104_1199.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1199.pure_subterms_within_computations);
            simplify = (uu___104_1199.simplify);
            erase_universes = (uu___104_1199.erase_universes);
            allow_unbound_universes = (uu___104_1199.allow_unbound_universes);
            reify_ = (uu___104_1199.reify_);
            compress_uvars = (uu___104_1199.compress_uvars);
            no_full_norm = (uu___104_1199.no_full_norm);
            check_no_uvars = (uu___104_1199.check_no_uvars);
            unmeta = (uu___104_1199.unmeta);
            unascribe = (uu___104_1199.unascribe)
          }
      | NoDeltaSteps  ->
          let uu___105_1200 = fs  in
          {
            beta = (uu___105_1200.beta);
            iota = (uu___105_1200.iota);
            zeta = (uu___105_1200.zeta);
            weak = (uu___105_1200.weak);
            hnf = (uu___105_1200.hnf);
            primops = (uu___105_1200.primops);
            eager_unfolding = (uu___105_1200.eager_unfolding);
            inlining = (uu___105_1200.inlining);
            no_delta_steps = true;
            unfold_until = (uu___105_1200.unfold_until);
            unfold_only = (uu___105_1200.unfold_only);
            unfold_attr = (uu___105_1200.unfold_attr);
            unfold_tac = (uu___105_1200.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1200.pure_subterms_within_computations);
            simplify = (uu___105_1200.simplify);
            erase_universes = (uu___105_1200.erase_universes);
            allow_unbound_universes = (uu___105_1200.allow_unbound_universes);
            reify_ = (uu___105_1200.reify_);
            compress_uvars = (uu___105_1200.compress_uvars);
            no_full_norm = (uu___105_1200.no_full_norm);
            check_no_uvars = (uu___105_1200.check_no_uvars);
            unmeta = (uu___105_1200.unmeta);
            unascribe = (uu___105_1200.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1202 = fs  in
          {
            beta = (uu___106_1202.beta);
            iota = (uu___106_1202.iota);
            zeta = (uu___106_1202.zeta);
            weak = (uu___106_1202.weak);
            hnf = (uu___106_1202.hnf);
            primops = (uu___106_1202.primops);
            eager_unfolding = (uu___106_1202.eager_unfolding);
            inlining = (uu___106_1202.inlining);
            no_delta_steps = (uu___106_1202.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1202.unfold_only);
            unfold_attr = (uu___106_1202.unfold_attr);
            unfold_tac = (uu___106_1202.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1202.pure_subterms_within_computations);
            simplify = (uu___106_1202.simplify);
            erase_universes = (uu___106_1202.erase_universes);
            allow_unbound_universes = (uu___106_1202.allow_unbound_universes);
            reify_ = (uu___106_1202.reify_);
            compress_uvars = (uu___106_1202.compress_uvars);
            no_full_norm = (uu___106_1202.no_full_norm);
            check_no_uvars = (uu___106_1202.check_no_uvars);
            unmeta = (uu___106_1202.unmeta);
            unascribe = (uu___106_1202.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1206 = fs  in
          {
            beta = (uu___107_1206.beta);
            iota = (uu___107_1206.iota);
            zeta = (uu___107_1206.zeta);
            weak = (uu___107_1206.weak);
            hnf = (uu___107_1206.hnf);
            primops = (uu___107_1206.primops);
            eager_unfolding = (uu___107_1206.eager_unfolding);
            inlining = (uu___107_1206.inlining);
            no_delta_steps = (uu___107_1206.no_delta_steps);
            unfold_until = (uu___107_1206.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___107_1206.unfold_attr);
            unfold_tac = (uu___107_1206.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1206.pure_subterms_within_computations);
            simplify = (uu___107_1206.simplify);
            erase_universes = (uu___107_1206.erase_universes);
            allow_unbound_universes = (uu___107_1206.allow_unbound_universes);
            reify_ = (uu___107_1206.reify_);
            compress_uvars = (uu___107_1206.compress_uvars);
            no_full_norm = (uu___107_1206.no_full_norm);
            check_no_uvars = (uu___107_1206.check_no_uvars);
            unmeta = (uu___107_1206.unmeta);
            unascribe = (uu___107_1206.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___108_1210 = fs  in
          {
            beta = (uu___108_1210.beta);
            iota = (uu___108_1210.iota);
            zeta = (uu___108_1210.zeta);
            weak = (uu___108_1210.weak);
            hnf = (uu___108_1210.hnf);
            primops = (uu___108_1210.primops);
            eager_unfolding = (uu___108_1210.eager_unfolding);
            inlining = (uu___108_1210.inlining);
            no_delta_steps = (uu___108_1210.no_delta_steps);
            unfold_until = (uu___108_1210.unfold_until);
            unfold_only = (uu___108_1210.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___108_1210.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1210.pure_subterms_within_computations);
            simplify = (uu___108_1210.simplify);
            erase_universes = (uu___108_1210.erase_universes);
            allow_unbound_universes = (uu___108_1210.allow_unbound_universes);
            reify_ = (uu___108_1210.reify_);
            compress_uvars = (uu___108_1210.compress_uvars);
            no_full_norm = (uu___108_1210.no_full_norm);
            check_no_uvars = (uu___108_1210.check_no_uvars);
            unmeta = (uu___108_1210.unmeta);
            unascribe = (uu___108_1210.unascribe)
          }
      | UnfoldTac  ->
          let uu___109_1211 = fs  in
          {
            beta = (uu___109_1211.beta);
            iota = (uu___109_1211.iota);
            zeta = (uu___109_1211.zeta);
            weak = (uu___109_1211.weak);
            hnf = (uu___109_1211.hnf);
            primops = (uu___109_1211.primops);
            eager_unfolding = (uu___109_1211.eager_unfolding);
            inlining = (uu___109_1211.inlining);
            no_delta_steps = (uu___109_1211.no_delta_steps);
            unfold_until = (uu___109_1211.unfold_until);
            unfold_only = (uu___109_1211.unfold_only);
            unfold_attr = (uu___109_1211.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___109_1211.pure_subterms_within_computations);
            simplify = (uu___109_1211.simplify);
            erase_universes = (uu___109_1211.erase_universes);
            allow_unbound_universes = (uu___109_1211.allow_unbound_universes);
            reify_ = (uu___109_1211.reify_);
            compress_uvars = (uu___109_1211.compress_uvars);
            no_full_norm = (uu___109_1211.no_full_norm);
            check_no_uvars = (uu___109_1211.check_no_uvars);
            unmeta = (uu___109_1211.unmeta);
            unascribe = (uu___109_1211.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___110_1212 = fs  in
          {
            beta = (uu___110_1212.beta);
            iota = (uu___110_1212.iota);
            zeta = (uu___110_1212.zeta);
            weak = (uu___110_1212.weak);
            hnf = (uu___110_1212.hnf);
            primops = (uu___110_1212.primops);
            eager_unfolding = (uu___110_1212.eager_unfolding);
            inlining = (uu___110_1212.inlining);
            no_delta_steps = (uu___110_1212.no_delta_steps);
            unfold_until = (uu___110_1212.unfold_until);
            unfold_only = (uu___110_1212.unfold_only);
            unfold_attr = (uu___110_1212.unfold_attr);
            unfold_tac = (uu___110_1212.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___110_1212.simplify);
            erase_universes = (uu___110_1212.erase_universes);
            allow_unbound_universes = (uu___110_1212.allow_unbound_universes);
            reify_ = (uu___110_1212.reify_);
            compress_uvars = (uu___110_1212.compress_uvars);
            no_full_norm = (uu___110_1212.no_full_norm);
            check_no_uvars = (uu___110_1212.check_no_uvars);
            unmeta = (uu___110_1212.unmeta);
            unascribe = (uu___110_1212.unascribe)
          }
      | Simplify  ->
          let uu___111_1213 = fs  in
          {
            beta = (uu___111_1213.beta);
            iota = (uu___111_1213.iota);
            zeta = (uu___111_1213.zeta);
            weak = (uu___111_1213.weak);
            hnf = (uu___111_1213.hnf);
            primops = (uu___111_1213.primops);
            eager_unfolding = (uu___111_1213.eager_unfolding);
            inlining = (uu___111_1213.inlining);
            no_delta_steps = (uu___111_1213.no_delta_steps);
            unfold_until = (uu___111_1213.unfold_until);
            unfold_only = (uu___111_1213.unfold_only);
            unfold_attr = (uu___111_1213.unfold_attr);
            unfold_tac = (uu___111_1213.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1213.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___111_1213.erase_universes);
            allow_unbound_universes = (uu___111_1213.allow_unbound_universes);
            reify_ = (uu___111_1213.reify_);
            compress_uvars = (uu___111_1213.compress_uvars);
            no_full_norm = (uu___111_1213.no_full_norm);
            check_no_uvars = (uu___111_1213.check_no_uvars);
            unmeta = (uu___111_1213.unmeta);
            unascribe = (uu___111_1213.unascribe)
          }
      | EraseUniverses  ->
          let uu___112_1214 = fs  in
          {
            beta = (uu___112_1214.beta);
            iota = (uu___112_1214.iota);
            zeta = (uu___112_1214.zeta);
            weak = (uu___112_1214.weak);
            hnf = (uu___112_1214.hnf);
            primops = (uu___112_1214.primops);
            eager_unfolding = (uu___112_1214.eager_unfolding);
            inlining = (uu___112_1214.inlining);
            no_delta_steps = (uu___112_1214.no_delta_steps);
            unfold_until = (uu___112_1214.unfold_until);
            unfold_only = (uu___112_1214.unfold_only);
            unfold_attr = (uu___112_1214.unfold_attr);
            unfold_tac = (uu___112_1214.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1214.pure_subterms_within_computations);
            simplify = (uu___112_1214.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___112_1214.allow_unbound_universes);
            reify_ = (uu___112_1214.reify_);
            compress_uvars = (uu___112_1214.compress_uvars);
            no_full_norm = (uu___112_1214.no_full_norm);
            check_no_uvars = (uu___112_1214.check_no_uvars);
            unmeta = (uu___112_1214.unmeta);
            unascribe = (uu___112_1214.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___113_1215 = fs  in
          {
            beta = (uu___113_1215.beta);
            iota = (uu___113_1215.iota);
            zeta = (uu___113_1215.zeta);
            weak = (uu___113_1215.weak);
            hnf = (uu___113_1215.hnf);
            primops = (uu___113_1215.primops);
            eager_unfolding = (uu___113_1215.eager_unfolding);
            inlining = (uu___113_1215.inlining);
            no_delta_steps = (uu___113_1215.no_delta_steps);
            unfold_until = (uu___113_1215.unfold_until);
            unfold_only = (uu___113_1215.unfold_only);
            unfold_attr = (uu___113_1215.unfold_attr);
            unfold_tac = (uu___113_1215.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1215.pure_subterms_within_computations);
            simplify = (uu___113_1215.simplify);
            erase_universes = (uu___113_1215.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___113_1215.reify_);
            compress_uvars = (uu___113_1215.compress_uvars);
            no_full_norm = (uu___113_1215.no_full_norm);
            check_no_uvars = (uu___113_1215.check_no_uvars);
            unmeta = (uu___113_1215.unmeta);
            unascribe = (uu___113_1215.unascribe)
          }
      | Reify  ->
          let uu___114_1216 = fs  in
          {
            beta = (uu___114_1216.beta);
            iota = (uu___114_1216.iota);
            zeta = (uu___114_1216.zeta);
            weak = (uu___114_1216.weak);
            hnf = (uu___114_1216.hnf);
            primops = (uu___114_1216.primops);
            eager_unfolding = (uu___114_1216.eager_unfolding);
            inlining = (uu___114_1216.inlining);
            no_delta_steps = (uu___114_1216.no_delta_steps);
            unfold_until = (uu___114_1216.unfold_until);
            unfold_only = (uu___114_1216.unfold_only);
            unfold_attr = (uu___114_1216.unfold_attr);
            unfold_tac = (uu___114_1216.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1216.pure_subterms_within_computations);
            simplify = (uu___114_1216.simplify);
            erase_universes = (uu___114_1216.erase_universes);
            allow_unbound_universes = (uu___114_1216.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___114_1216.compress_uvars);
            no_full_norm = (uu___114_1216.no_full_norm);
            check_no_uvars = (uu___114_1216.check_no_uvars);
            unmeta = (uu___114_1216.unmeta);
            unascribe = (uu___114_1216.unascribe)
          }
      | CompressUvars  ->
          let uu___115_1217 = fs  in
          {
            beta = (uu___115_1217.beta);
            iota = (uu___115_1217.iota);
            zeta = (uu___115_1217.zeta);
            weak = (uu___115_1217.weak);
            hnf = (uu___115_1217.hnf);
            primops = (uu___115_1217.primops);
            eager_unfolding = (uu___115_1217.eager_unfolding);
            inlining = (uu___115_1217.inlining);
            no_delta_steps = (uu___115_1217.no_delta_steps);
            unfold_until = (uu___115_1217.unfold_until);
            unfold_only = (uu___115_1217.unfold_only);
            unfold_attr = (uu___115_1217.unfold_attr);
            unfold_tac = (uu___115_1217.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1217.pure_subterms_within_computations);
            simplify = (uu___115_1217.simplify);
            erase_universes = (uu___115_1217.erase_universes);
            allow_unbound_universes = (uu___115_1217.allow_unbound_universes);
            reify_ = (uu___115_1217.reify_);
            compress_uvars = true;
            no_full_norm = (uu___115_1217.no_full_norm);
            check_no_uvars = (uu___115_1217.check_no_uvars);
            unmeta = (uu___115_1217.unmeta);
            unascribe = (uu___115_1217.unascribe)
          }
      | NoFullNorm  ->
          let uu___116_1218 = fs  in
          {
            beta = (uu___116_1218.beta);
            iota = (uu___116_1218.iota);
            zeta = (uu___116_1218.zeta);
            weak = (uu___116_1218.weak);
            hnf = (uu___116_1218.hnf);
            primops = (uu___116_1218.primops);
            eager_unfolding = (uu___116_1218.eager_unfolding);
            inlining = (uu___116_1218.inlining);
            no_delta_steps = (uu___116_1218.no_delta_steps);
            unfold_until = (uu___116_1218.unfold_until);
            unfold_only = (uu___116_1218.unfold_only);
            unfold_attr = (uu___116_1218.unfold_attr);
            unfold_tac = (uu___116_1218.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1218.pure_subterms_within_computations);
            simplify = (uu___116_1218.simplify);
            erase_universes = (uu___116_1218.erase_universes);
            allow_unbound_universes = (uu___116_1218.allow_unbound_universes);
            reify_ = (uu___116_1218.reify_);
            compress_uvars = (uu___116_1218.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___116_1218.check_no_uvars);
            unmeta = (uu___116_1218.unmeta);
            unascribe = (uu___116_1218.unascribe)
          }
      | CheckNoUvars  ->
          let uu___117_1219 = fs  in
          {
            beta = (uu___117_1219.beta);
            iota = (uu___117_1219.iota);
            zeta = (uu___117_1219.zeta);
            weak = (uu___117_1219.weak);
            hnf = (uu___117_1219.hnf);
            primops = (uu___117_1219.primops);
            eager_unfolding = (uu___117_1219.eager_unfolding);
            inlining = (uu___117_1219.inlining);
            no_delta_steps = (uu___117_1219.no_delta_steps);
            unfold_until = (uu___117_1219.unfold_until);
            unfold_only = (uu___117_1219.unfold_only);
            unfold_attr = (uu___117_1219.unfold_attr);
            unfold_tac = (uu___117_1219.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1219.pure_subterms_within_computations);
            simplify = (uu___117_1219.simplify);
            erase_universes = (uu___117_1219.erase_universes);
            allow_unbound_universes = (uu___117_1219.allow_unbound_universes);
            reify_ = (uu___117_1219.reify_);
            compress_uvars = (uu___117_1219.compress_uvars);
            no_full_norm = (uu___117_1219.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___117_1219.unmeta);
            unascribe = (uu___117_1219.unascribe)
          }
      | Unmeta  ->
          let uu___118_1220 = fs  in
          {
            beta = (uu___118_1220.beta);
            iota = (uu___118_1220.iota);
            zeta = (uu___118_1220.zeta);
            weak = (uu___118_1220.weak);
            hnf = (uu___118_1220.hnf);
            primops = (uu___118_1220.primops);
            eager_unfolding = (uu___118_1220.eager_unfolding);
            inlining = (uu___118_1220.inlining);
            no_delta_steps = (uu___118_1220.no_delta_steps);
            unfold_until = (uu___118_1220.unfold_until);
            unfold_only = (uu___118_1220.unfold_only);
            unfold_attr = (uu___118_1220.unfold_attr);
            unfold_tac = (uu___118_1220.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1220.pure_subterms_within_computations);
            simplify = (uu___118_1220.simplify);
            erase_universes = (uu___118_1220.erase_universes);
            allow_unbound_universes = (uu___118_1220.allow_unbound_universes);
            reify_ = (uu___118_1220.reify_);
            compress_uvars = (uu___118_1220.compress_uvars);
            no_full_norm = (uu___118_1220.no_full_norm);
            check_no_uvars = (uu___118_1220.check_no_uvars);
            unmeta = true;
            unascribe = (uu___118_1220.unascribe)
          }
      | Unascribe  ->
          let uu___119_1221 = fs  in
          {
            beta = (uu___119_1221.beta);
            iota = (uu___119_1221.iota);
            zeta = (uu___119_1221.zeta);
            weak = (uu___119_1221.weak);
            hnf = (uu___119_1221.hnf);
            primops = (uu___119_1221.primops);
            eager_unfolding = (uu___119_1221.eager_unfolding);
            inlining = (uu___119_1221.inlining);
            no_delta_steps = (uu___119_1221.no_delta_steps);
            unfold_until = (uu___119_1221.unfold_until);
            unfold_only = (uu___119_1221.unfold_only);
            unfold_attr = (uu___119_1221.unfold_attr);
            unfold_tac = (uu___119_1221.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1221.pure_subterms_within_computations);
            simplify = (uu___119_1221.simplify);
            erase_universes = (uu___119_1221.erase_universes);
            allow_unbound_universes = (uu___119_1221.allow_unbound_universes);
            reify_ = (uu___119_1221.reify_);
            compress_uvars = (uu___119_1221.compress_uvars);
            no_full_norm = (uu___119_1221.no_full_norm);
            check_no_uvars = (uu___119_1221.check_no_uvars);
            unmeta = (uu___119_1221.unmeta);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1253  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1454 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1556 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1567 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___77_1586  ->
    match uu___77_1586 with
    | Clos (uu____1587,t,uu____1589,uu____1590) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1635 -> "Univ"
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
  primitive_steps: primitive_step FStar_Util.psmap ;
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
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
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
  
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             FStar_Util.psmap_add m1 (FStar_Ident.text_of_lid p.name) p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____1897 = FStar_Util.psmap_empty ()  in add_steps uu____1897 l
  
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
    match projectee with | Arg _0 -> true | uu____2041 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2077 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2113 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2182 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2224 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2280 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2320 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2352 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2388 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2404 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____2429 .
    'Auu____2429 ->
      FStar_Range.range -> 'Auu____2429 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2483 = FStar_ST.op_Bang r  in
          match uu____2483 with
          | FStar_Pervasives_Native.Some uu____2531 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2585 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2585 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2592  ->
    match uu___78_2592 with
    | Arg (c,uu____2594,uu____2595) ->
        let uu____2596 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2596
    | MemoLazy uu____2597 -> "MemoLazy"
    | Abs (uu____2604,bs,uu____2606,uu____2607,uu____2608) ->
        let uu____2613 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2613
    | UnivArgs uu____2618 -> "UnivArgs"
    | Match uu____2625 -> "Match"
    | App (uu____2632,t,uu____2634,uu____2635) ->
        let uu____2636 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2636
    | Meta (m,uu____2638) -> "Meta"
    | Let uu____2639 -> "Let"
    | Cfg uu____2648 -> "Cfg"
    | Debug (t,uu____2650) ->
        let uu____2651 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2651
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2659 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2659 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2690 . 'Auu____2690 Prims.list -> Prims.bool =
  fun uu___79_2696  ->
    match uu___79_2696 with | [] -> true | uu____2699 -> false
  
let lookup_bvar :
  'Auu____2706 'Auu____2707 .
    ('Auu____2707,'Auu____2706) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2706
  =
  fun env  ->
    fun x  ->
      try
        let uu____2731 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2731
      with
      | uu____2744 ->
          let uu____2745 =
            let uu____2746 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2746  in
          failwith uu____2745
  
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
          let uu____2783 =
            FStar_List.fold_left
              (fun uu____2809  ->
                 fun u1  ->
                   match uu____2809 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2834 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2834 with
                        | (k_u,n1) ->
                            let uu____2849 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2849
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2783 with
          | (uu____2867,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2892 =
                   let uu____2893 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2893  in
                 match uu____2892 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2911 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2919 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2925 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2934 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2943 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2950 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2950 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2967 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2967 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2975 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2983 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2983 with
                                  | (uu____2988,m) -> n1 <= m))
                           in
                        if uu____2975 then rest1 else us1
                    | uu____2993 -> us1)
               | uu____2998 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3002 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3002
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3006 = aux u  in
           match uu____3006 with
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
          (fun uu____3110  ->
             let uu____3111 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3112 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3111
               uu____3112);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3119 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3121 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3146 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3147 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3148 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3149 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3166 =
                      let uu____3167 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3168 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3167 uu____3168
                       in
                    failwith uu____3166
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3171 =
                    let uu____3172 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3172  in
                  mk uu____3171 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3179 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3179
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3181 = lookup_bvar env x  in
                  (match uu____3181 with
                   | Univ uu____3184 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3187,uu____3188) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3300 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3300 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3328 =
                         let uu____3329 =
                           let uu____3346 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3346)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3329  in
                       mk uu____3328 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3377 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3377 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3419 =
                    let uu____3430 =
                      let uu____3437 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3437]  in
                    closures_as_binders_delayed cfg env uu____3430  in
                  (match uu____3419 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3455 =
                         let uu____3456 =
                           let uu____3463 =
                             let uu____3464 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3464
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3463, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3456  in
                       mk uu____3455 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3555 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3555
                    | FStar_Util.Inr c ->
                        let uu____3569 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3569
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3585 =
                    let uu____3586 =
                      let uu____3613 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3613, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3586  in
                  mk uu____3585 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3664 =
                    let uu____3665 =
                      let uu____3672 = closure_as_term_delayed cfg env t'  in
                      let uu____3675 =
                        let uu____3676 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3676  in
                      (uu____3672, uu____3675)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3665  in
                  mk uu____3664 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3736 =
                    let uu____3737 =
                      let uu____3744 = closure_as_term_delayed cfg env t'  in
                      let uu____3747 =
                        let uu____3748 =
                          let uu____3755 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3755)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3748  in
                      (uu____3744, uu____3747)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3737  in
                  mk uu____3736 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3774 =
                    let uu____3775 =
                      let uu____3782 = closure_as_term_delayed cfg env t'  in
                      let uu____3785 =
                        let uu____3786 =
                          let uu____3795 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3795)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3786  in
                      (uu____3782, uu____3785)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3775  in
                  mk uu____3774 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3808 =
                    let uu____3809 =
                      let uu____3816 = closure_as_term_delayed cfg env t'  in
                      (uu____3816, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3809  in
                  mk uu____3808 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3856  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3875 =
                    let uu____3886 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3886
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3905 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___124_3917 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_3917.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_3917.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3905))
                     in
                  (match uu____3875 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___125_3933 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___125_3933.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___125_3933.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___125_3933.FStar_Syntax_Syntax.lbattrs)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3944,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4003  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4028 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4028
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4048  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4070 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4070
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___126_4082 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_4082.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_4082.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___127_4083 = lb  in
                    let uu____4084 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___127_4083.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___127_4083.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4084;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___127_4083.FStar_Syntax_Syntax.lbattrs)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4114  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4203 =
                    match uu____4203 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4258 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4279 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4339  ->
                                        fun uu____4340  ->
                                          match (uu____4339, uu____4340) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4431 =
                                                norm_pat env3 p1  in
                                              (match uu____4431 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4279 with
                               | (pats1,env3) ->
                                   ((let uu___128_4513 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___128_4513.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___129_4532 = x  in
                                let uu____4533 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4532.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4532.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4533
                                }  in
                              ((let uu___130_4547 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4547.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___131_4558 = x  in
                                let uu____4559 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4558.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4558.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4559
                                }  in
                              ((let uu___132_4573 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4573.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___133_4589 = x  in
                                let uu____4590 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___133_4589.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___133_4589.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4590
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___134_4597 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___134_4597.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4600 = norm_pat env1 pat  in
                        (match uu____4600 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4629 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4629
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4635 =
                    let uu____4636 =
                      let uu____4659 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4659)  in
                    FStar_Syntax_Syntax.Tm_match uu____4636  in
                  mk uu____4635 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4745 -> closure_as_term cfg env t

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
        | uu____4771 ->
            FStar_List.map
              (fun uu____4788  ->
                 match uu____4788 with
                 | (x,imp) ->
                     let uu____4807 = closure_as_term_delayed cfg env x  in
                     (uu____4807, imp)) args

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
        let uu____4821 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4870  ->
                  fun uu____4871  ->
                    match (uu____4870, uu____4871) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___135_4941 = b  in
                          let uu____4942 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___135_4941.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___135_4941.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4942
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4821 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5035 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5048 = closure_as_term_delayed cfg env t  in
                 let uu____5049 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5048 uu____5049
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5062 = closure_as_term_delayed cfg env t  in
                 let uu____5063 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5062 uu____5063
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
                        (fun uu___80_5089  ->
                           match uu___80_5089 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5093 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5093
                           | f -> f))
                    in
                 let uu____5097 =
                   let uu___136_5098 = c1  in
                   let uu____5099 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5099;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___136_5098.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5097)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5109  ->
            match uu___81_5109 with
            | FStar_Syntax_Syntax.DECREASES uu____5110 -> false
            | uu____5113 -> true))

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
                   (fun uu___82_5131  ->
                      match uu___82_5131 with
                      | FStar_Syntax_Syntax.DECREASES uu____5132 -> false
                      | uu____5135 -> true))
               in
            let rc1 =
              let uu___137_5137 = rc  in
              let uu____5138 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___137_5137.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5138;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5145 -> lopt

let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
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
    let uu____5230 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5230  in
  let arg_as_bounded_int uu____5258 =
    match uu____5258 with
    | (a,uu____5270) ->
        let uu____5277 =
          let uu____5278 = FStar_Syntax_Subst.compress a  in
          uu____5278.FStar_Syntax_Syntax.n  in
        (match uu____5277 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5288;
                FStar_Syntax_Syntax.vars = uu____5289;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5291;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5292;_},uu____5293)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5332 =
               let uu____5337 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5337)  in
             FStar_Pervasives_Native.Some uu____5332
         | uu____5342 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5382 = f a  in FStar_Pervasives_Native.Some uu____5382
    | uu____5383 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5431 = f a0 a1  in FStar_Pervasives_Native.Some uu____5431
    | uu____5432 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5474 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5474)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5523 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5523)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5547 =
    match uu____5547 with
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
                   let uu____5595 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5595)) a429 a430)
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
                       let uu____5623 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5623)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5644 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5644)) a436
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
                       let uu____5672 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5672)) a439
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
                       let uu____5700 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5700))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5808 =
          let uu____5817 = as_a a  in
          let uu____5820 = as_b b  in (uu____5817, uu____5820)  in
        (match uu____5808 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5835 =
               let uu____5836 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5836  in
             FStar_Pervasives_Native.Some uu____5835
         | uu____5837 -> FStar_Pervasives_Native.None)
    | uu____5846 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5860 =
        let uu____5861 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5861  in
      mk uu____5860 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5871 =
      let uu____5874 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5874  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5871  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5906 =
      let uu____5907 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5907  in
    FStar_Syntax_Embeddings.embed_int rng uu____5906  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5925 = arg_as_string a1  in
        (match uu____5925 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5931 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5931 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5944 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5944
              | uu____5945 -> FStar_Pervasives_Native.None)
         | uu____5950 -> FStar_Pervasives_Native.None)
    | uu____5953 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5963 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5963  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5987 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5998 =
          let uu____6019 = arg_as_string fn  in
          let uu____6022 = arg_as_int from_line  in
          let uu____6025 = arg_as_int from_col  in
          let uu____6028 = arg_as_int to_line  in
          let uu____6031 = arg_as_int to_col  in
          (uu____6019, uu____6022, uu____6025, uu____6028, uu____6031)  in
        (match uu____5998 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6062 =
                 let uu____6063 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6064 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6063 uu____6064  in
               let uu____6065 =
                 let uu____6066 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6067 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6066 uu____6067  in
               FStar_Range.mk_range fn1 uu____6062 uu____6065  in
             let uu____6068 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____6068
         | uu____6073 -> FStar_Pervasives_Native.None)
    | uu____6094 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6121)::(a1,uu____6123)::(a2,uu____6125)::[] ->
        let uu____6162 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6162 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6175 -> FStar_Pervasives_Native.None)
    | uu____6176 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6203)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6212 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6236 =
      let uu____6251 =
        let uu____6266 =
          let uu____6281 =
            let uu____6296 =
              let uu____6311 =
                let uu____6326 =
                  let uu____6341 =
                    let uu____6356 =
                      let uu____6371 =
                        let uu____6386 =
                          let uu____6401 =
                            let uu____6416 =
                              let uu____6431 =
                                let uu____6446 =
                                  let uu____6461 =
                                    let uu____6476 =
                                      let uu____6491 =
                                        let uu____6506 =
                                          let uu____6521 =
                                            let uu____6536 =
                                              let uu____6551 =
                                                let uu____6564 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6564,
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
                                              let uu____6571 =
                                                let uu____6586 =
                                                  let uu____6599 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6599,
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
                                                let uu____6606 =
                                                  let uu____6621 =
                                                    let uu____6636 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6636,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6645 =
                                                    let uu____6662 =
                                                      let uu____6677 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6677,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6686 =
                                                      let uu____6703 =
                                                        let uu____6722 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6722,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6703]  in
                                                    uu____6662 :: uu____6686
                                                     in
                                                  uu____6621 :: uu____6645
                                                   in
                                                uu____6586 :: uu____6606  in
                                              uu____6551 :: uu____6571  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6536
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6521
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
                                          :: uu____6506
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
                                        :: uu____6491
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
                                      :: uu____6476
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
                                                        let uu____6939 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6939 y)) a466
                                                a467 a468)))
                                    :: uu____6461
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6446
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6431
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6416
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6401
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6386
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6371
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
                                          let uu____7106 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7106)) a470 a471 a472)))
                      :: uu____6356
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
                                        let uu____7132 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7132)) a474 a475 a476)))
                    :: uu____6341
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
                                      let uu____7158 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7158)) a478 a479 a480)))
                  :: uu____6326
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
                                    let uu____7184 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7184)) a482 a483 a484)))
                :: uu____6311
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6296
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6281
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6266
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6251
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6236
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7337 =
        let uu____7338 =
          let uu____7339 = FStar_Syntax_Syntax.as_arg c  in [uu____7339]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7338  in
      uu____7337 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7389 =
                let uu____7402 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7402, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7418  ->
                                    fun uu____7419  ->
                                      match (uu____7418, uu____7419) with
                                      | ((int_to_t1,x),(uu____7438,y)) ->
                                          let uu____7448 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7448)) a486 a487 a488)))
                 in
              let uu____7449 =
                let uu____7464 =
                  let uu____7477 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7477, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7493  ->
                                      fun uu____7494  ->
                                        match (uu____7493, uu____7494) with
                                        | ((int_to_t1,x),(uu____7513,y)) ->
                                            let uu____7523 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7523)) a490 a491 a492)))
                   in
                let uu____7524 =
                  let uu____7539 =
                    let uu____7552 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7552, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7568  ->
                                        fun uu____7569  ->
                                          match (uu____7568, uu____7569) with
                                          | ((int_to_t1,x),(uu____7588,y)) ->
                                              let uu____7598 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7598)) a494 a495 a496)))
                     in
                  let uu____7599 =
                    let uu____7614 =
                      let uu____7627 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7627, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7639  ->
                                        match uu____7639 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7614]  in
                  uu____7539 :: uu____7599  in
                uu____7464 :: uu____7524  in
              uu____7389 :: uu____7449))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7753 =
                let uu____7766 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7766, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7782  ->
                                    fun uu____7783  ->
                                      match (uu____7782, uu____7783) with
                                      | ((int_to_t1,x),(uu____7802,y)) ->
                                          let uu____7812 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7812)) a501 a502 a503)))
                 in
              let uu____7813 =
                let uu____7828 =
                  let uu____7841 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7841, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7857  ->
                                      fun uu____7858  ->
                                        match (uu____7857, uu____7858) with
                                        | ((int_to_t1,x),(uu____7877,y)) ->
                                            let uu____7887 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7887)) a505 a506 a507)))
                   in
                [uu____7828]  in
              uu____7753 :: uu____7813))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let uu____7936 =
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  FStar_All.pipe_left prim_from_list uu____7936 
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7984)::(a1,uu____7986)::(a2,uu____7988)::[] ->
        let uu____8025 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8025 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8031 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8031.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8031.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8035 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8035.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8035.FStar_Syntax_Syntax.vars)
                })
         | uu____8036 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8038)::uu____8039::(a1,uu____8041)::(a2,uu____8043)::[] ->
        let uu____8092 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8092 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8098 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8098.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8098.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8102 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8102.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8102.FStar_Syntax_Syntax.vars)
                })
         | uu____8103 -> FStar_Pervasives_Native.None)
    | uu____8104 -> failwith "Unexpected number of arguments"  in
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
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____8123 =
        let uu____8124 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____8124 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____8123
    with | uu____8130 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____8134 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8134) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8194  ->
           fun subst1  ->
             match uu____8194 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8235,uu____8236)) ->
                      let uu____8295 = b  in
                      (match uu____8295 with
                       | (bv,uu____8303) ->
                           let uu____8304 =
                             let uu____8305 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____8305  in
                           if uu____8304
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8310 = unembed_binder term1  in
                              match uu____8310 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8317 =
                                      let uu___142_8318 = bv  in
                                      let uu____8319 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___142_8318.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___142_8318.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8319
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8317
                                     in
                                  let b_for_x =
                                    let uu____8323 =
                                      let uu____8330 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8330)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8323  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8339  ->
                                         match uu___83_8339 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8340,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8342;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8343;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8348 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8349 -> subst1)) env []
  
let reduce_primops :
  'Auu____8366 'Auu____8367 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8367) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8366 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8409 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8409 with
             | (head1,args) ->
                 let uu____8446 =
                   let uu____8447 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8447.FStar_Syntax_Syntax.n  in
                 (match uu____8446 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8451 =
                        FStar_Util.psmap_try_find cfg.primitive_steps
                          (FStar_Ident.text_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                         in
                      (match uu____8451 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8466  ->
                                   let uu____8467 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8468 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8475 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8467 uu____8468 uu____8475);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8480  ->
                                   let uu____8481 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8481);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8484  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8486 =
                                 prim_step.interpretation psc args  in
                               match uu____8486 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8492  ->
                                         let uu____8493 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8493);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8499  ->
                                         let uu____8500 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8501 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8500 uu____8501);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8502 ->
                           (log_primops cfg
                              (fun uu____8506  ->
                                 let uu____8507 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8507);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8511  ->
                            let uu____8512 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8512);
                       (match args with
                        | (a1,uu____8514)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8531 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8543  ->
                            let uu____8544 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8544);
                       (match args with
                        | (t,uu____8546)::(r,uu____8548)::[] ->
                            let uu____8575 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8575 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___143_8579 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___143_8579.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___143_8579.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8582 -> tm))
                  | uu____8591 -> tm))
  
let reduce_equality :
  'Auu____8596 'Auu____8597 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8597) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8596 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___144_8635 = cfg  in
         {
           steps =
             (let uu___145_8638 = default_steps  in
              {
                beta = (uu___145_8638.beta);
                iota = (uu___145_8638.iota);
                zeta = (uu___145_8638.zeta);
                weak = (uu___145_8638.weak);
                hnf = (uu___145_8638.hnf);
                primops = true;
                eager_unfolding = (uu___145_8638.eager_unfolding);
                inlining = (uu___145_8638.inlining);
                no_delta_steps = (uu___145_8638.no_delta_steps);
                unfold_until = (uu___145_8638.unfold_until);
                unfold_only = (uu___145_8638.unfold_only);
                unfold_attr = (uu___145_8638.unfold_attr);
                unfold_tac = (uu___145_8638.unfold_tac);
                pure_subterms_within_computations =
                  (uu___145_8638.pure_subterms_within_computations);
                simplify = (uu___145_8638.simplify);
                erase_universes = (uu___145_8638.erase_universes);
                allow_unbound_universes =
                  (uu___145_8638.allow_unbound_universes);
                reify_ = (uu___145_8638.reify_);
                compress_uvars = (uu___145_8638.compress_uvars);
                no_full_norm = (uu___145_8638.no_full_norm);
                check_no_uvars = (uu___145_8638.check_no_uvars);
                unmeta = (uu___145_8638.unmeta);
                unascribe = (uu___145_8638.unascribe)
              });
           tcenv = (uu___144_8635.tcenv);
           debug = (uu___144_8635.debug);
           delta_level = (uu___144_8635.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___144_8635.strong);
           memoize_lazy = (uu___144_8635.memoize_lazy);
           normalize_pure_lets = (uu___144_8635.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8645 'Auu____8646 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8646) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8645 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8688 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8688
          then tm1
          else
            (let w t =
               let uu___146_8700 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___146_8700.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___146_8700.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8716;
                      FStar_Syntax_Syntax.vars = uu____8717;_},uu____8718)
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
                      FStar_Syntax_Syntax.pos = uu____8725;
                      FStar_Syntax_Syntax.vars = uu____8726;_},uu____8727)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8733 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8738 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8738
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8759 =
                 match uu____8759 with
                 | (t1,q) ->
                     let uu____8772 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8772 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8800 -> (t1, q))
                  in
               let uu____8809 = FStar_Syntax_Util.head_and_args t  in
               match uu____8809 with
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
                         FStar_Syntax_Syntax.pos = uu____8906;
                         FStar_Syntax_Syntax.vars = uu____8907;_},uu____8908);
                    FStar_Syntax_Syntax.pos = uu____8909;
                    FStar_Syntax_Syntax.vars = uu____8910;_},args)
                 ->
                 let uu____8936 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8936
                 then
                   let uu____8937 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8937 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8992)::
                        (uu____8993,(arg,uu____8995))::[] ->
                        maybe_auto_squash arg
                    | (uu____9060,(arg,uu____9062))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9063)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9128)::uu____9129::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9192::(FStar_Pervasives_Native.Some (false
                                   ),uu____9193)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9256 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9272 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9272
                    then
                      let uu____9273 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9273 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9328)::uu____9329::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9392::(FStar_Pervasives_Native.Some (true
                                     ),uu____9393)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9456)::
                          (uu____9457,(arg,uu____9459))::[] ->
                          maybe_auto_squash arg
                      | (uu____9524,(arg,uu____9526))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9527)::[]
                          -> maybe_auto_squash arg
                      | uu____9592 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9608 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9608
                       then
                         let uu____9609 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9609 with
                         | uu____9664::(FStar_Pervasives_Native.Some (true
                                        ),uu____9665)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9728)::uu____9729::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9792)::
                             (uu____9793,(arg,uu____9795))::[] ->
                             maybe_auto_squash arg
                         | (uu____9860,(p,uu____9862))::(uu____9863,(q,uu____9865))::[]
                             ->
                             let uu____9930 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9930
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9932 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9948 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9948
                          then
                            let uu____9949 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9949 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10004)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10043)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10082 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10098 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10098
                             then
                               match args with
                               | (t,uu____10100)::[] ->
                                   let uu____10117 =
                                     let uu____10118 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10118.FStar_Syntax_Syntax.n  in
                                   (match uu____10117 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10121::[],body,uu____10123) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10150 -> tm1)
                                    | uu____10153 -> tm1)
                               | (uu____10154,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10155))::
                                   (t,uu____10157)::[] ->
                                   let uu____10196 =
                                     let uu____10197 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10197.FStar_Syntax_Syntax.n  in
                                   (match uu____10196 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10200::[],body,uu____10202) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10229 -> tm1)
                                    | uu____10232 -> tm1)
                               | uu____10233 -> tm1
                             else
                               (let uu____10243 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10243
                                then
                                  match args with
                                  | (t,uu____10245)::[] ->
                                      let uu____10262 =
                                        let uu____10263 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10263.FStar_Syntax_Syntax.n  in
                                      (match uu____10262 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10266::[],body,uu____10268)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10295 -> tm1)
                                       | uu____10298 -> tm1)
                                  | (uu____10299,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10300))::(t,uu____10302)::[] ->
                                      let uu____10341 =
                                        let uu____10342 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10342.FStar_Syntax_Syntax.n  in
                                      (match uu____10341 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10345::[],body,uu____10347)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10374 -> tm1)
                                       | uu____10377 -> tm1)
                                  | uu____10378 -> tm1
                                else
                                  (let uu____10388 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10388
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10389;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10390;_},uu____10391)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10408;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10409;_},uu____10410)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10427 -> tm1
                                   else
                                     (let uu____10437 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10437 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10457 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10467;
                    FStar_Syntax_Syntax.vars = uu____10468;_},args)
                 ->
                 let uu____10490 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____10490
                 then
                   let uu____10491 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____10491 with
                    | (FStar_Pervasives_Native.Some (true ),uu____10546)::
                        (uu____10547,(arg,uu____10549))::[] ->
                        maybe_auto_squash arg
                    | (uu____10614,(arg,uu____10616))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____10617)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____10682)::uu____10683::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10746::(FStar_Pervasives_Native.Some (false
                                    ),uu____10747)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10810 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____10826 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____10826
                    then
                      let uu____10827 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____10827 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10882)::uu____10883::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10946::(FStar_Pervasives_Native.Some (true
                                      ),uu____10947)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11010)::
                          (uu____11011,(arg,uu____11013))::[] ->
                          maybe_auto_squash arg
                      | (uu____11078,(arg,uu____11080))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11081)::[]
                          -> maybe_auto_squash arg
                      | uu____11146 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11162 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11162
                       then
                         let uu____11163 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11163 with
                         | uu____11218::(FStar_Pervasives_Native.Some (true
                                         ),uu____11219)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11282)::uu____11283::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11346)::
                             (uu____11347,(arg,uu____11349))::[] ->
                             maybe_auto_squash arg
                         | (uu____11414,(p,uu____11416))::(uu____11417,
                                                           (q,uu____11419))::[]
                             ->
                             let uu____11484 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____11484
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11486 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____11502 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____11502
                          then
                            let uu____11503 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____11503 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____11558)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____11597)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____11636 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____11652 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____11652
                             then
                               match args with
                               | (t,uu____11654)::[] ->
                                   let uu____11671 =
                                     let uu____11672 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11672.FStar_Syntax_Syntax.n  in
                                   (match uu____11671 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11675::[],body,uu____11677) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11704 -> tm1)
                                    | uu____11707 -> tm1)
                               | (uu____11708,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____11709))::
                                   (t,uu____11711)::[] ->
                                   let uu____11750 =
                                     let uu____11751 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11751.FStar_Syntax_Syntax.n  in
                                   (match uu____11750 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11754::[],body,uu____11756) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11783 -> tm1)
                                    | uu____11786 -> tm1)
                               | uu____11787 -> tm1
                             else
                               (let uu____11797 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____11797
                                then
                                  match args with
                                  | (t,uu____11799)::[] ->
                                      let uu____11816 =
                                        let uu____11817 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11817.FStar_Syntax_Syntax.n  in
                                      (match uu____11816 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11820::[],body,uu____11822)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11849 -> tm1)
                                       | uu____11852 -> tm1)
                                  | (uu____11853,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____11854))::(t,uu____11856)::[] ->
                                      let uu____11895 =
                                        let uu____11896 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11896.FStar_Syntax_Syntax.n  in
                                      (match uu____11895 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11899::[],body,uu____11901)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11928 -> tm1)
                                       | uu____11931 -> tm1)
                                  | uu____11932 -> tm1
                                else
                                  (let uu____11942 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____11942
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11943;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11944;_},uu____11945)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11962;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11963;_},uu____11964)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11981 -> tm1
                                   else
                                     (let uu____11991 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____11991 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____12011 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____12026 -> tm1)
  
let maybe_simplify :
  'Auu____12033 'Auu____12034 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____12034) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____12033 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____12077 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12078 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____12077
               uu____12078)
          else ();
          tm'
  
let is_norm_request :
  'Auu____12084 .
    FStar_Syntax_Syntax.term -> 'Auu____12084 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____12097 =
        let uu____12104 =
          let uu____12105 = FStar_Syntax_Util.un_uinst hd1  in
          uu____12105.FStar_Syntax_Syntax.n  in
        (uu____12104, args)  in
      match uu____12097 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12111::uu____12112::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12116::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____12121::uu____12122::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____12125 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_12136  ->
    match uu___84_12136 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12142 =
          let uu____12145 =
            let uu____12146 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____12146  in
          [uu____12145]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____12142
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12162 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____12162) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____12215 =
            let uu____12218 =
              let uu____12221 =
                let uu____12226 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____12226 s  in
              FStar_All.pipe_right uu____12221 FStar_Util.must  in
            FStar_All.pipe_right uu____12218 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____12215
        with | uu____12254 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____12265::(tm,uu____12267)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____12296)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____12317)::uu____12318::(tm,uu____12320)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let uu____12357 =
            let uu____12362 = full_norm steps  in parse_steps uu____12362  in
          (match uu____12357 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____12401 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_12418  ->
    match uu___85_12418 with
    | (App
        (uu____12421,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12422;
                       FStar_Syntax_Syntax.vars = uu____12423;_},uu____12424,uu____12425))::uu____12426
        -> true
    | uu____12433 -> false
  
let firstn :
  'Auu____12439 .
    Prims.int ->
      'Auu____12439 Prims.list ->
        ('Auu____12439 Prims.list,'Auu____12439 Prims.list)
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
          (uu____12475,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12476;
                         FStar_Syntax_Syntax.vars = uu____12477;_},uu____12478,uu____12479))::uu____12480
          -> (cfg.steps).reify_
      | uu____12487 -> false
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let r =
        let uu____12497 = FStar_Syntax_Util.eq_tm a a'  in
        match uu____12497 with
        | FStar_Syntax_Util.Equal  -> true
        | uu____12498 -> false  in
      r
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12640 ->
                   let uu____12665 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12665
               | uu____12666 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12674  ->
               let uu____12675 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12676 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12677 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12684 =
                 let uu____12685 =
                   let uu____12688 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12688
                    in
                 stack_to_string uu____12685  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12675 uu____12676 uu____12677 uu____12684);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12711 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12712 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12713;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12714;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12717;
                 FStar_Syntax_Syntax.fv_delta = uu____12718;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12719;
                 FStar_Syntax_Syntax.fv_delta = uu____12720;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12721);_}
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
                 let uu___149_12763 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___149_12763.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___149_12763.FStar_Syntax_Syntax.vars)
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
                 let uu___150_12801 = cfg  in
                 {
                   steps =
                     (let uu___151_12804 = cfg.steps  in
                      {
                        beta = (uu___151_12804.beta);
                        iota = (uu___151_12804.iota);
                        zeta = (uu___151_12804.zeta);
                        weak = (uu___151_12804.weak);
                        hnf = (uu___151_12804.hnf);
                        primops = (uu___151_12804.primops);
                        eager_unfolding = (uu___151_12804.eager_unfolding);
                        inlining = (uu___151_12804.inlining);
                        no_delta_steps = false;
                        unfold_until = (uu___151_12804.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___151_12804.unfold_attr);
                        unfold_tac = (uu___151_12804.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___151_12804.pure_subterms_within_computations);
                        simplify = (uu___151_12804.simplify);
                        erase_universes = (uu___151_12804.erase_universes);
                        allow_unbound_universes =
                          (uu___151_12804.allow_unbound_universes);
                        reify_ = (uu___151_12804.reify_);
                        compress_uvars = (uu___151_12804.compress_uvars);
                        no_full_norm = (uu___151_12804.no_full_norm);
                        check_no_uvars = (uu___151_12804.check_no_uvars);
                        unmeta = (uu___151_12804.unmeta);
                        unascribe = (uu___151_12804.unascribe)
                      });
                   tcenv = (uu___150_12801.tcenv);
                   debug = (uu___150_12801.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___150_12801.primitive_steps);
                   strong = (uu___150_12801.strong);
                   memoize_lazy = (uu___150_12801.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12807 = get_norm_request (norm cfg' env []) args  in
               (match uu____12807 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12838  ->
                              fun stack1  ->
                                match uu____12838 with
                                | (a,aq) ->
                                    let uu____12850 =
                                      let uu____12851 =
                                        let uu____12858 =
                                          let uu____12859 =
                                            let uu____12890 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12890, false)  in
                                          Clos uu____12859  in
                                        (uu____12858, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12851  in
                                    uu____12850 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12974  ->
                          let uu____12975 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12975);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12997 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_13002  ->
                                match uu___86_13002 with
                                | UnfoldUntil uu____13003 -> true
                                | UnfoldOnly uu____13004 -> true
                                | uu____13007 -> false))
                         in
                      if uu____12997
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___152_13012 = cfg  in
                      let uu____13013 = to_fsteps s  in
                      {
                        steps = uu____13013;
                        tcenv = (uu___152_13012.tcenv);
                        debug = (uu___152_13012.debug);
                        delta_level;
                        primitive_steps = (uu___152_13012.primitive_steps);
                        strong = (uu___152_13012.strong);
                        memoize_lazy = (uu___152_13012.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____13022 =
                          let uu____13023 =
                            let uu____13028 = FStar_Util.now ()  in
                            (t1, uu____13028)  in
                          Debug uu____13023  in
                        uu____13022 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____13032 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13032
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____13041 =
                      let uu____13048 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____13048, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____13041  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____13058 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____13058  in
               let uu____13059 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____13059
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____13065  ->
                       let uu____13066 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13067 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____13066 uu____13067);
                  if b
                  then
                    (let uu____13068 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____13068 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___87_13077  ->
                            match uu___87_13077 with
                            | FStar_TypeChecker_Env.UnfoldTac  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.Inlining  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  let should_delta1 =
                    if Prims.op_Negation should_delta
                    then false
                    else
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____13087 =
                             cases
                               (FStar_Util.for_some
                                  (attr_eq FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____13087))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____13106) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some (attr_eq at) ats')
                                   ats
                             | (uu____13141,uu____13142) -> false)))
                     in
                  log cfg
                    (fun uu____13164  ->
                       let uu____13165 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13166 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13167 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____13165
                         uu____13166 uu____13167);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____13170 = lookup_bvar env x  in
               (match uu____13170 with
                | Univ uu____13173 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____13222 = FStar_ST.op_Bang r  in
                      (match uu____13222 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____13340  ->
                                 let uu____13341 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____13342 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____13341
                                   uu____13342);
                            (let uu____13343 =
                               let uu____13344 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____13344.FStar_Syntax_Syntax.n  in
                             match uu____13343 with
                             | FStar_Syntax_Syntax.Tm_abs uu____13347 ->
                                 norm cfg env2 stack t'
                             | uu____13364 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13434)::uu____13435 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____13444)::uu____13445 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____13455,uu____13456))::stack_rest ->
                    (match c with
                     | Univ uu____13460 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13469 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13490  ->
                                    let uu____13491 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13491);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13531  ->
                                    let uu____13532 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13532);
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
                       (fun uu____13610  ->
                          let uu____13611 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13611);
                     norm cfg env stack1 t1)
                | (Debug uu____13612)::uu____13613 ->
                    if (cfg.steps).weak
                    then
                      let uu____13620 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13620
                    else
                      (let uu____13622 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13622 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13664  -> dummy :: env1) env)
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
                                          let uu____13701 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13701)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_13706 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_13706.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_13706.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13707 -> lopt  in
                           (log cfg
                              (fun uu____13713  ->
                                 let uu____13714 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13714);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_13723 = cfg  in
                               {
                                 steps = (uu___154_13723.steps);
                                 tcenv = (uu___154_13723.tcenv);
                                 debug = (uu___154_13723.debug);
                                 delta_level = (uu___154_13723.delta_level);
                                 primitive_steps =
                                   (uu___154_13723.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_13723.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_13723.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13734)::uu____13735 ->
                    if (cfg.steps).weak
                    then
                      let uu____13742 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13742
                    else
                      (let uu____13744 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13744 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13786  -> dummy :: env1) env)
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
                                          let uu____13823 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13823)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_13828 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_13828.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_13828.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13829 -> lopt  in
                           (log cfg
                              (fun uu____13835  ->
                                 let uu____13836 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13836);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_13845 = cfg  in
                               {
                                 steps = (uu___154_13845.steps);
                                 tcenv = (uu___154_13845.tcenv);
                                 debug = (uu___154_13845.debug);
                                 delta_level = (uu___154_13845.delta_level);
                                 primitive_steps =
                                   (uu___154_13845.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_13845.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_13845.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13856)::uu____13857 ->
                    if (cfg.steps).weak
                    then
                      let uu____13868 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13868
                    else
                      (let uu____13870 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13870 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13912  -> dummy :: env1) env)
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
                                          let uu____13949 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13949)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_13954 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_13954.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_13954.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13955 -> lopt  in
                           (log cfg
                              (fun uu____13961  ->
                                 let uu____13962 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13962);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_13971 = cfg  in
                               {
                                 steps = (uu___154_13971.steps);
                                 tcenv = (uu___154_13971.tcenv);
                                 debug = (uu___154_13971.debug);
                                 delta_level = (uu___154_13971.delta_level);
                                 primitive_steps =
                                   (uu___154_13971.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_13971.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_13971.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13982)::uu____13983 ->
                    if (cfg.steps).weak
                    then
                      let uu____13994 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13994
                    else
                      (let uu____13996 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13996 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14038  -> dummy :: env1) env)
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
                                          let uu____14075 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14075)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_14080 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_14080.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_14080.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14081 -> lopt  in
                           (log cfg
                              (fun uu____14087  ->
                                 let uu____14088 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14088);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_14097 = cfg  in
                               {
                                 steps = (uu___154_14097.steps);
                                 tcenv = (uu___154_14097.tcenv);
                                 debug = (uu___154_14097.debug);
                                 delta_level = (uu___154_14097.delta_level);
                                 primitive_steps =
                                   (uu___154_14097.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_14097.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_14097.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____14108)::uu____14109 ->
                    if (cfg.steps).weak
                    then
                      let uu____14124 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14124
                    else
                      (let uu____14126 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14126 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14168  -> dummy :: env1) env)
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
                                          let uu____14205 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14205)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_14210 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_14210.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_14210.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14211 -> lopt  in
                           (log cfg
                              (fun uu____14217  ->
                                 let uu____14218 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14218);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_14227 = cfg  in
                               {
                                 steps = (uu___154_14227.steps);
                                 tcenv = (uu___154_14227.tcenv);
                                 debug = (uu___154_14227.debug);
                                 delta_level = (uu___154_14227.delta_level);
                                 primitive_steps =
                                   (uu___154_14227.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_14227.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_14227.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____14238 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14238
                    else
                      (let uu____14240 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14240 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14282  -> dummy :: env1) env)
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
                                          let uu____14319 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14319)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_14324 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_14324.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_14324.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14325 -> lopt  in
                           (log cfg
                              (fun uu____14331  ->
                                 let uu____14332 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14332);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_14341 = cfg  in
                               {
                                 steps = (uu___154_14341.steps);
                                 tcenv = (uu___154_14341.tcenv);
                                 debug = (uu___154_14341.debug);
                                 delta_level = (uu___154_14341.delta_level);
                                 primitive_steps =
                                   (uu___154_14341.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_14341.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_14341.normalize_pure_lets)
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
                      (fun uu____14390  ->
                         fun stack1  ->
                           match uu____14390 with
                           | (a,aq) ->
                               let uu____14402 =
                                 let uu____14403 =
                                   let uu____14410 =
                                     let uu____14411 =
                                       let uu____14442 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____14442, false)  in
                                     Clos uu____14411  in
                                   (uu____14410, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____14403  in
                               uu____14402 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14526  ->
                     let uu____14527 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14527);
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
                             ((let uu___155_14563 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_14563.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_14563.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14564 ->
                      let uu____14569 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14569)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14572 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14572 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14603 =
                          let uu____14604 =
                            let uu____14611 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___156_14613 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___156_14613.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___156_14613.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14611)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14604  in
                        mk uu____14603 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14632 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14632
               else
                 (let uu____14634 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14634 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14642 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14666  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14642 c1  in
                      let t2 =
                        let uu____14688 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14688 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14799)::uu____14800 ->
                    (log cfg
                       (fun uu____14811  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14812)::uu____14813 ->
                    (log cfg
                       (fun uu____14824  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14825,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14826;
                                   FStar_Syntax_Syntax.vars = uu____14827;_},uu____14828,uu____14829))::uu____14830
                    ->
                    (log cfg
                       (fun uu____14839  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14840)::uu____14841 ->
                    (log cfg
                       (fun uu____14852  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14853 ->
                    (log cfg
                       (fun uu____14856  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14860  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14877 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14877
                         | FStar_Util.Inr c ->
                             let uu____14885 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14885
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14898 =
                               let uu____14899 =
                                 let uu____14926 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14926, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14899
                                in
                             mk uu____14898 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14945 ->
                           let uu____14946 =
                             let uu____14947 =
                               let uu____14948 =
                                 let uu____14975 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14975, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14948
                                in
                             mk uu____14947 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14946))))
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
                         let uu____15085 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____15085 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___157_15105 = cfg  in
                               let uu____15106 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___157_15105.steps);
                                 tcenv = uu____15106;
                                 debug = (uu___157_15105.debug);
                                 delta_level = (uu___157_15105.delta_level);
                                 primitive_steps =
                                   (uu___157_15105.primitive_steps);
                                 strong = (uu___157_15105.strong);
                                 memoize_lazy = (uu___157_15105.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___157_15105.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____15111 =
                                 let uu____15112 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____15112  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____15111
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___158_15115 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___158_15115.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___158_15115.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___158_15115.FStar_Syntax_Syntax.lbattrs)
                             }))
                  in
               let uu____15116 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____15116
           | FStar_Syntax_Syntax.Tm_let
               ((uu____15127,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____15128;
                               FStar_Syntax_Syntax.lbunivs = uu____15129;
                               FStar_Syntax_Syntax.lbtyp = uu____15130;
                               FStar_Syntax_Syntax.lbeff = uu____15131;
                               FStar_Syntax_Syntax.lbdef = uu____15132;
                               FStar_Syntax_Syntax.lbattrs = uu____15133;_}::uu____15134),uu____15135)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____15175 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.is_fvar
                              FStar_Parser_Const.inline_let_attr)
                           lb.FStar_Syntax_Syntax.lbattrs))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Util.for_some
                                (FStar_Syntax_Util.is_fvar
                                   FStar_Parser_Const.inline_let_attr)
                                lb.FStar_Syntax_Syntax.lbattrs))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____15175
               then
                 let binder =
                   let uu____15177 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____15177  in
                 let env1 =
                   let uu____15187 =
                     let uu____15194 =
                       let uu____15195 =
                         let uu____15226 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____15226,
                           false)
                          in
                       Clos uu____15195  in
                     ((FStar_Pervasives_Native.Some binder), uu____15194)  in
                   uu____15187 :: env  in
                 (log cfg
                    (fun uu____15319  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____15323  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____15324 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____15324))
                 else
                   (let uu____15326 =
                      let uu____15331 =
                        let uu____15332 =
                          let uu____15333 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____15333
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____15332]  in
                      FStar_Syntax_Subst.open_term uu____15331 body  in
                    match uu____15326 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____15342  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____15350 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____15350  in
                            FStar_Util.Inl
                              (let uu___159_15360 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_15360.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_15360.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____15363  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___160_15365 = lb  in
                             let uu____15366 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___160_15365.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___160_15365.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15366;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___160_15365.FStar_Syntax_Syntax.lbattrs)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15401  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___161_15424 = cfg  in
                             {
                               steps = (uu___161_15424.steps);
                               tcenv = (uu___161_15424.tcenv);
                               debug = (uu___161_15424.debug);
                               delta_level = (uu___161_15424.delta_level);
                               primitive_steps =
                                 (uu___161_15424.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___161_15424.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___161_15424.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15427  ->
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
               let uu____15444 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15444 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15480 =
                               let uu___162_15481 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___162_15481.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___162_15481.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15480  in
                           let uu____15482 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15482 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15508 =
                                   FStar_List.map (fun uu____15524  -> dummy)
                                     lbs1
                                    in
                                 let uu____15525 =
                                   let uu____15534 =
                                     FStar_List.map
                                       (fun uu____15554  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15534 env  in
                                 FStar_List.append uu____15508 uu____15525
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15578 =
                                       let uu___163_15579 = rc  in
                                       let uu____15580 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___163_15579.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15580;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___163_15579.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15578
                                 | uu____15587 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___164_15591 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___164_15591.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___164_15591.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___164_15591.FStar_Syntax_Syntax.lbattrs)
                               }) lbs1
                       in
                    let env' =
                      let uu____15601 =
                        FStar_List.map (fun uu____15617  -> dummy) lbs2  in
                      FStar_List.append uu____15601 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15625 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15625 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___165_15641 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___165_15641.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___165_15641.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15668 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15668
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15687 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15763  ->
                        match uu____15763 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___166_15884 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_15884.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___166_15884.FStar_Syntax_Syntax.sort)
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
               (match uu____15687 with
                | (rec_env,memos,uu____16097) ->
                    let uu____16150 =
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
                             let uu____16461 =
                               let uu____16468 =
                                 let uu____16469 =
                                   let uu____16500 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16500, false)
                                    in
                                 Clos uu____16469  in
                               (FStar_Pervasives_Native.None, uu____16468)
                                in
                             uu____16461 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16610  ->
                     let uu____16611 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16611);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16633 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16635::uu____16636 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16641) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16642 ->
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
                             | uu____16673 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16687 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16687
                              | uu____16698 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16702 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16728 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16746 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16763 =
                        let uu____16764 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16765 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16764 uu____16765
                         in
                      failwith uu____16763
                    else rebuild cfg env stack t2
                | uu____16767 -> norm cfg env stack t2))

and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let r_env =
                let uu____16777 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16777  in
              let uu____16778 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16778 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16791  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16802  ->
                        let uu____16803 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16804 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16803 uu____16804);
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
                      | (UnivArgs (us',uu____16817))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env)
                             in
                          norm cfg env1 stack1 t1
                      | uu____16872 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____16875 ->
                          let uu____16878 =
                            let uu____16879 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16879
                             in
                          failwith uu____16878
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
                  let uu___167_16900 = cfg  in
                  let uu____16901 =
                    to_fsteps
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      Inlining]
                     in
                  {
                    steps = uu____16901;
                    tcenv = (uu___167_16900.tcenv);
                    debug = (uu___167_16900.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___167_16900.primitive_steps);
                    strong = (uu___167_16900.strong);
                    memoize_lazy = (uu___167_16900.memoize_lazy);
                    normalize_pure_lets =
                      (uu___167_16900.normalize_pure_lets)
                  }
                else
                  (let uu___168_16903 = cfg  in
                   {
                     steps =
                       (let uu___169_16906 = cfg.steps  in
                        {
                          beta = (uu___169_16906.beta);
                          iota = (uu___169_16906.iota);
                          zeta = false;
                          weak = (uu___169_16906.weak);
                          hnf = (uu___169_16906.hnf);
                          primops = (uu___169_16906.primops);
                          eager_unfolding = (uu___169_16906.eager_unfolding);
                          inlining = (uu___169_16906.inlining);
                          no_delta_steps = (uu___169_16906.no_delta_steps);
                          unfold_until = (uu___169_16906.unfold_until);
                          unfold_only = (uu___169_16906.unfold_only);
                          unfold_attr = (uu___169_16906.unfold_attr);
                          unfold_tac = (uu___169_16906.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___169_16906.pure_subterms_within_computations);
                          simplify = (uu___169_16906.simplify);
                          erase_universes = (uu___169_16906.erase_universes);
                          allow_unbound_universes =
                            (uu___169_16906.allow_unbound_universes);
                          reify_ = (uu___169_16906.reify_);
                          compress_uvars = (uu___169_16906.compress_uvars);
                          no_full_norm = (uu___169_16906.no_full_norm);
                          check_no_uvars = (uu___169_16906.check_no_uvars);
                          unmeta = (uu___169_16906.unmeta);
                          unascribe = (uu___169_16906.unascribe)
                        });
                     tcenv = (uu___168_16903.tcenv);
                     debug = (uu___168_16903.debug);
                     delta_level = (uu___168_16903.delta_level);
                     primitive_steps = (uu___168_16903.primitive_steps);
                     strong = (uu___168_16903.strong);
                     memoize_lazy = (uu___168_16903.memoize_lazy);
                     normalize_pure_lets =
                       (uu___168_16903.normalize_pure_lets)
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
                  (fun uu____16936  ->
                     let uu____16937 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16938 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16937
                       uu____16938);
                (let uu____16939 =
                   let uu____16940 = FStar_Syntax_Subst.compress head2  in
                   uu____16940.FStar_Syntax_Syntax.n  in
                 match uu____16939 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16958 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16958 with
                      | (uu____16959,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16965 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16973 =
                                   let uu____16974 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16974.FStar_Syntax_Syntax.n  in
                                 match uu____16973 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16980,uu____16981))
                                     ->
                                     let uu____16990 =
                                       let uu____16991 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16991.FStar_Syntax_Syntax.n  in
                                     (match uu____16990 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16997,msrc,uu____16999))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____17008 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____17008
                                      | uu____17009 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____17010 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____17011 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____17011 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___170_17016 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___170_17016.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___170_17016.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___170_17016.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___170_17016.FStar_Syntax_Syntax.lbattrs)
                                      }  in
                                    let uu____17017 = FStar_List.tl stack  in
                                    let uu____17018 =
                                      let uu____17019 =
                                        let uu____17022 =
                                          let uu____17023 =
                                            let uu____17036 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____17036)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____17023
                                           in
                                        FStar_Syntax_Syntax.mk uu____17022
                                         in
                                      uu____17019
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____17017 uu____17018
                                | FStar_Pervasives_Native.None  ->
                                    let uu____17052 =
                                      let uu____17053 = is_return body  in
                                      match uu____17053 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____17057;
                                            FStar_Syntax_Syntax.vars =
                                              uu____17058;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____17063 -> false  in
                                    if uu____17052
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
                                         let uu____17086 =
                                           let uu____17089 =
                                             let uu____17090 =
                                               let uu____17107 =
                                                 let uu____17110 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____17110]  in
                                               (uu____17107, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____17090
                                              in
                                           FStar_Syntax_Syntax.mk uu____17089
                                            in
                                         uu____17086
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____17126 =
                                           let uu____17127 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____17127.FStar_Syntax_Syntax.n
                                            in
                                         match uu____17126 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____17133::uu____17134::[])
                                             ->
                                             let uu____17141 =
                                               let uu____17144 =
                                                 let uu____17145 =
                                                   let uu____17152 =
                                                     let uu____17155 =
                                                       let uu____17156 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____17156
                                                        in
                                                     let uu____17157 =
                                                       let uu____17160 =
                                                         let uu____17161 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____17161
                                                          in
                                                       [uu____17160]  in
                                                     uu____17155 ::
                                                       uu____17157
                                                      in
                                                   (bind1, uu____17152)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____17145
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____17144
                                                in
                                             uu____17141
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____17169 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____17175 =
                                           let uu____17178 =
                                             let uu____17179 =
                                               let uu____17194 =
                                                 let uu____17197 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____17198 =
                                                   let uu____17201 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____17202 =
                                                     let uu____17205 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____17206 =
                                                       let uu____17209 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____17210 =
                                                         let uu____17213 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____17214 =
                                                           let uu____17217 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____17217]  in
                                                         uu____17213 ::
                                                           uu____17214
                                                          in
                                                       uu____17209 ::
                                                         uu____17210
                                                        in
                                                     uu____17205 ::
                                                       uu____17206
                                                      in
                                                   uu____17201 :: uu____17202
                                                    in
                                                 uu____17197 :: uu____17198
                                                  in
                                               (bind_inst, uu____17194)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____17179
                                              in
                                           FStar_Syntax_Syntax.mk uu____17178
                                            in
                                         uu____17175
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____17229  ->
                                            let uu____17230 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____17231 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____17230 uu____17231);
                                       (let uu____17232 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____17232 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____17256 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17256 with
                      | (uu____17257,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17292 =
                                  let uu____17293 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____17293.FStar_Syntax_Syntax.n  in
                                match uu____17292 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17299) -> t2
                                | uu____17304 -> head3  in
                              let uu____17305 =
                                let uu____17306 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17306.FStar_Syntax_Syntax.n  in
                              match uu____17305 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17312 -> FStar_Pervasives_Native.None
                               in
                            let uu____17313 = maybe_extract_fv head3  in
                            match uu____17313 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17323 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17323
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____17328 = maybe_extract_fv head4
                                     in
                                  match uu____17328 with
                                  | FStar_Pervasives_Native.Some uu____17333
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17334 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____17339 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17354 =
                              match uu____17354 with
                              | (e,q) ->
                                  let uu____17361 =
                                    let uu____17362 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17362.FStar_Syntax_Syntax.n  in
                                  (match uu____17361 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____17377 -> false)
                               in
                            let uu____17378 =
                              let uu____17379 =
                                let uu____17386 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17386 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17379
                               in
                            if uu____17378
                            then
                              let uu____17391 =
                                let uu____17392 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17392
                                 in
                              failwith uu____17391
                            else ());
                           (let uu____17394 = maybe_unfold_action head_app
                               in
                            match uu____17394 with
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
                                   (fun uu____17435  ->
                                      let uu____17436 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17437 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17436 uu____17437);
                                 (let uu____17438 = FStar_List.tl stack  in
                                  norm cfg env uu____17438 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17440) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17464 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17464  in
                     (log cfg
                        (fun uu____17468  ->
                           let uu____17469 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17469);
                      (let uu____17470 = FStar_List.tl stack  in
                       norm cfg env uu____17470 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____17472) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17597  ->
                               match uu____17597 with
                               | (pat,wopt,tm) ->
                                   let uu____17645 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17645)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____17677 = FStar_List.tl stack  in
                     norm cfg env uu____17677 tm
                 | uu____17678 -> fallback ())

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
              (fun uu____17692  ->
                 let uu____17693 = FStar_Ident.string_of_lid msrc  in
                 let uu____17694 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17695 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17693
                   uu____17694 uu____17695);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____17697 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17697 with
               | (uu____17698,return_repr) ->
                   let return_inst =
                     let uu____17707 =
                       let uu____17708 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17708.FStar_Syntax_Syntax.n  in
                     match uu____17707 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17714::[]) ->
                         let uu____17721 =
                           let uu____17724 =
                             let uu____17725 =
                               let uu____17732 =
                                 let uu____17735 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17735]  in
                               (return_tm, uu____17732)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17725  in
                           FStar_Syntax_Syntax.mk uu____17724  in
                         uu____17721 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17743 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17746 =
                     let uu____17749 =
                       let uu____17750 =
                         let uu____17765 =
                           let uu____17768 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17769 =
                             let uu____17772 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17772]  in
                           uu____17768 :: uu____17769  in
                         (return_inst, uu____17765)  in
                       FStar_Syntax_Syntax.Tm_app uu____17750  in
                     FStar_Syntax_Syntax.mk uu____17749  in
                   uu____17746 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17781 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17781 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17784 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17784
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17785;
                     FStar_TypeChecker_Env.mtarget = uu____17786;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17787;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17802 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17802
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17803;
                     FStar_TypeChecker_Env.mtarget = uu____17804;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17805;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17829 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17830 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17829 t FStar_Syntax_Syntax.tun uu____17830)

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
                (fun uu____17886  ->
                   match uu____17886 with
                   | (a,imp) ->
                       let uu____17897 = norm cfg env [] a  in
                       (uu____17897, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___171_17911 = comp  in
            let uu____17912 =
              let uu____17913 =
                let uu____17922 = norm cfg env [] t  in
                let uu____17923 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17922, uu____17923)  in
              FStar_Syntax_Syntax.Total uu____17913  in
            {
              FStar_Syntax_Syntax.n = uu____17912;
              FStar_Syntax_Syntax.pos =
                (uu___171_17911.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___171_17911.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___172_17938 = comp  in
            let uu____17939 =
              let uu____17940 =
                let uu____17949 = norm cfg env [] t  in
                let uu____17950 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17949, uu____17950)  in
              FStar_Syntax_Syntax.GTotal uu____17940  in
            {
              FStar_Syntax_Syntax.n = uu____17939;
              FStar_Syntax_Syntax.pos =
                (uu___172_17938.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___172_17938.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____18002  ->
                      match uu____18002 with
                      | (a,i) ->
                          let uu____18013 = norm cfg env [] a  in
                          (uu____18013, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_18024  ->
                      match uu___88_18024 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____18028 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____18028
                      | f -> f))
               in
            let uu___173_18032 = comp  in
            let uu____18033 =
              let uu____18034 =
                let uu___174_18035 = ct  in
                let uu____18036 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____18037 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____18040 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____18036;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___174_18035.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____18037;
                  FStar_Syntax_Syntax.effect_args = uu____18040;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____18034  in
            {
              FStar_Syntax_Syntax.n = uu____18033;
              FStar_Syntax_Syntax.pos =
                (uu___173_18032.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_18032.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____18051  ->
        match uu____18051 with
        | (x,imp) ->
            let uu____18054 =
              let uu___175_18055 = x  in
              let uu____18056 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___175_18055.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___175_18055.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18056
              }  in
            (uu____18054, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18062 =
          FStar_List.fold_left
            (fun uu____18080  ->
               fun b  ->
                 match uu____18080 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18062 with | (nbs,uu____18120) -> FStar_List.rev nbs

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
            let uu____18136 =
              let uu___176_18137 = rc  in
              let uu____18138 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___176_18137.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18138;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___176_18137.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18136
        | uu____18145 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____18158  ->
               let uu____18159 = FStar_Syntax_Print.tag_of_term t  in
               let uu____18160 = FStar_Syntax_Print.term_to_string t  in
               let uu____18161 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____18168 =
                 let uu____18169 =
                   let uu____18172 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____18172
                    in
                 stack_to_string uu____18169  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____18159 uu____18160 uu____18161 uu____18168);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____18203 =
                     let uu____18204 =
                       let uu____18205 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____18205  in
                     FStar_Util.string_of_int uu____18204  in
                   let uu____18210 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____18211 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____18203 uu____18210 uu____18211)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____18265  ->
                     let uu____18266 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____18266);
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
               let uu____18302 =
                 let uu___177_18303 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___177_18303.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___177_18303.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____18302
           | (Arg (Univ uu____18304,uu____18305,uu____18306))::uu____18307 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____18310,uu____18311))::uu____18312 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____18328),aq,r))::stack1 ->
               (log cfg
                  (fun uu____18381  ->
                     let uu____18382 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____18382);
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
                  (let uu____18392 = FStar_ST.op_Bang m  in
                   match uu____18392 with
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
                   | FStar_Pervasives_Native.Some (uu____18529,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____18576 =
                 log cfg
                   (fun uu____18580  ->
                      let uu____18581 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18581);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____18585 =
                 let uu____18586 = FStar_Syntax_Subst.compress t1  in
                 uu____18586.FStar_Syntax_Syntax.n  in
               (match uu____18585 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18613 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____18613  in
                    (log cfg
                       (fun uu____18617  ->
                          let uu____18618 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18618);
                     (let uu____18619 = FStar_List.tl stack  in
                      norm cfg env1 uu____18619 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18620);
                       FStar_Syntax_Syntax.pos = uu____18621;
                       FStar_Syntax_Syntax.vars = uu____18622;_},(e,uu____18624)::[])
                    -> norm cfg env1 stack' e
                | uu____18653 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18673  ->
                     let uu____18674 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18674);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____18679 =
                   log cfg
                     (fun uu____18684  ->
                        let uu____18685 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____18686 =
                          let uu____18687 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18704  ->
                                    match uu____18704 with
                                    | (p,uu____18714,uu____18715) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____18687
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18685 uu____18686);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_18732  ->
                                match uu___89_18732 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18733 -> false))
                         in
                      let uu___178_18734 = cfg  in
                      {
                        steps =
                          (let uu___179_18737 = cfg.steps  in
                           {
                             beta = (uu___179_18737.beta);
                             iota = (uu___179_18737.iota);
                             zeta = false;
                             weak = (uu___179_18737.weak);
                             hnf = (uu___179_18737.hnf);
                             primops = (uu___179_18737.primops);
                             eager_unfolding =
                               (uu___179_18737.eager_unfolding);
                             inlining = (uu___179_18737.inlining);
                             no_delta_steps = (uu___179_18737.no_delta_steps);
                             unfold_until = (uu___179_18737.unfold_until);
                             unfold_only = (uu___179_18737.unfold_only);
                             unfold_attr = (uu___179_18737.unfold_attr);
                             unfold_tac = (uu___179_18737.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___179_18737.pure_subterms_within_computations);
                             simplify = (uu___179_18737.simplify);
                             erase_universes =
                               (uu___179_18737.erase_universes);
                             allow_unbound_universes =
                               (uu___179_18737.allow_unbound_universes);
                             reify_ = (uu___179_18737.reify_);
                             compress_uvars = (uu___179_18737.compress_uvars);
                             no_full_norm = (uu___179_18737.no_full_norm);
                             check_no_uvars = (uu___179_18737.check_no_uvars);
                             unmeta = (uu___179_18737.unmeta);
                             unascribe = (uu___179_18737.unascribe)
                           });
                        tcenv = (uu___178_18734.tcenv);
                        debug = (uu___178_18734.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___178_18734.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___178_18734.memoize_lazy);
                        normalize_pure_lets =
                          (uu___178_18734.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18769 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18790 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18850  ->
                                    fun uu____18851  ->
                                      match (uu____18850, uu____18851) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18942 = norm_pat env3 p1
                                             in
                                          (match uu____18942 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____18790 with
                           | (pats1,env3) ->
                               ((let uu___180_19024 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___180_19024.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___181_19043 = x  in
                            let uu____19044 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_19043.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_19043.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____19044
                            }  in
                          ((let uu___182_19058 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_19058.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___183_19069 = x  in
                            let uu____19070 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_19069.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_19069.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____19070
                            }  in
                          ((let uu___184_19084 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___184_19084.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___185_19100 = x  in
                            let uu____19101 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___185_19100.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___185_19100.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____19101
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___186_19108 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___186_19108.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____19118 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____19132 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____19132 with
                                  | (p,wopt,e) ->
                                      let uu____19152 = norm_pat env1 p  in
                                      (match uu____19152 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____19177 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____19177
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____19183 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____19183)
                    in
                 let rec is_cons head1 =
                   let uu____19188 =
                     let uu____19189 = FStar_Syntax_Subst.compress head1  in
                     uu____19189.FStar_Syntax_Syntax.n  in
                   match uu____19188 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____19193) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____19198 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____19199;
                         FStar_Syntax_Syntax.fv_delta = uu____19200;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____19201;
                         FStar_Syntax_Syntax.fv_delta = uu____19202;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____19203);_}
                       -> true
                   | uu____19210 -> false  in
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
                   let uu____19355 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____19355 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____19442 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19481 ->
                                 let uu____19482 =
                                   let uu____19483 = is_cons head1  in
                                   Prims.op_Negation uu____19483  in
                                 FStar_Util.Inr uu____19482)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19508 =
                              let uu____19509 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____19509.FStar_Syntax_Syntax.n  in
                            (match uu____19508 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19527 ->
                                 let uu____19528 =
                                   let uu____19529 = is_cons head1  in
                                   Prims.op_Negation uu____19529  in
                                 FStar_Util.Inr uu____19528))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19598)::rest_a,(p1,uu____19601)::rest_p) ->
                       let uu____19645 = matches_pat t2 p1  in
                       (match uu____19645 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19694 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19800 = matches_pat scrutinee1 p1  in
                       (match uu____19800 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19840  ->
                                  let uu____19841 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____19842 =
                                    let uu____19843 =
                                      FStar_List.map
                                        (fun uu____19853  ->
                                           match uu____19853 with
                                           | (uu____19858,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____19843
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19841 uu____19842);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19889  ->
                                       match uu____19889 with
                                       | (bv,t2) ->
                                           let uu____19912 =
                                             let uu____19919 =
                                               let uu____19922 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____19922
                                                in
                                             let uu____19923 =
                                               let uu____19924 =
                                                 let uu____19955 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____19955, false)
                                                  in
                                               Clos uu____19924  in
                                             (uu____19919, uu____19923)  in
                                           uu____19912 :: env2) env1 s
                                 in
                              let uu____20072 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____20072)))
                    in
                 if Prims.op_Negation (cfg.steps).iota
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (config' :
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___90_20100  ->
                  match uu___90_20100 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____20104 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____20110 -> d  in
        let uu____20113 = to_fsteps s  in
        let uu____20114 =
          let uu____20115 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____20116 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____20117 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____20118 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____20119 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____20115;
            primop = uu____20116;
            b380 = uu____20117;
            norm_delayed = uu____20118;
            print_normalized = uu____20119
          }  in
        let uu____20120 = add_steps built_in_primitive_steps psteps  in
        let uu____20123 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____20125 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____20125)
           in
        {
          steps = uu____20113;
          tcenv = e;
          debug = uu____20114;
          delta_level = d1;
          primitive_steps = uu____20120;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____20123
        }
  
let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  -> fun e  -> config' [] s e 
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e  in norm c [] [] t
  
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
      fun t  -> let uu____20183 = config s e  in norm_comp uu____20183 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____20196 = config [] env  in norm_universe uu____20196 [] u
  
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
        let uu____20214 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____20214  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____20221 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___187_20240 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___187_20240.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___187_20240.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____20247 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____20247
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
                  let uu___188_20256 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___188_20256.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___188_20256.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___188_20256.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___189_20258 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___189_20258.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___189_20258.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___189_20258.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___189_20258.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___190_20259 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___190_20259.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___190_20259.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____20261 -> c
  
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
        let uu____20273 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____20273  in
      let uu____20280 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____20280
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____20284  ->
                 let uu____20285 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____20285)
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
            ((let uu____20302 =
                let uu____20307 =
                  let uu____20308 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____20308
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____20307)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____20302);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____20319 = config [AllowUnboundUniverses] env  in
          norm_comp uu____20319 [] c
        with
        | e ->
            ((let uu____20332 =
                let uu____20337 =
                  let uu____20338 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____20338
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____20337)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____20332);
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
                   let uu____20375 =
                     let uu____20376 =
                       let uu____20383 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____20383)  in
                     FStar_Syntax_Syntax.Tm_refine uu____20376  in
                   mk uu____20375 t01.FStar_Syntax_Syntax.pos
               | uu____20388 -> t2)
          | uu____20389 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [Primops;
        Weak;
        HNF;
        UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
        Beta] env t
  
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
        let uu____20429 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____20429 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____20458 ->
                 let uu____20465 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____20465 with
                  | (actuals,uu____20475,uu____20476) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____20490 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____20490 with
                         | (binders,args) ->
                             let uu____20507 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____20507
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
      | uu____20515 ->
          let uu____20516 = FStar_Syntax_Util.head_and_args t  in
          (match uu____20516 with
           | (head1,args) ->
               let uu____20553 =
                 let uu____20554 = FStar_Syntax_Subst.compress head1  in
                 uu____20554.FStar_Syntax_Syntax.n  in
               (match uu____20553 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20557,thead) ->
                    let uu____20583 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____20583 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20625 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___195_20633 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___195_20633.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___195_20633.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___195_20633.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___195_20633.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___195_20633.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___195_20633.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___195_20633.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___195_20633.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___195_20633.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___195_20633.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___195_20633.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___195_20633.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___195_20633.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___195_20633.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___195_20633.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___195_20633.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___195_20633.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___195_20633.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___195_20633.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___195_20633.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___195_20633.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___195_20633.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___195_20633.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___195_20633.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___195_20633.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___195_20633.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___195_20633.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___195_20633.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___195_20633.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___195_20633.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___195_20633.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___195_20633.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____20625 with
                            | (uu____20634,ty,uu____20636) ->
                                eta_expand_with_type env t ty))
                | uu____20637 ->
                    let uu____20638 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___196_20646 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___196_20646.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___196_20646.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___196_20646.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___196_20646.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___196_20646.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___196_20646.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___196_20646.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___196_20646.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___196_20646.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___196_20646.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___196_20646.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___196_20646.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___196_20646.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___196_20646.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___196_20646.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___196_20646.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___196_20646.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___196_20646.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___196_20646.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___196_20646.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___196_20646.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___196_20646.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___196_20646.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___196_20646.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___196_20646.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___196_20646.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___196_20646.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___196_20646.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___196_20646.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___196_20646.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___196_20646.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___196_20646.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____20638 with
                     | (uu____20647,ty,uu____20649) ->
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
      let uu___197_20706 = x  in
      let uu____20707 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___197_20706.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___197_20706.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20707
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20710 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20735 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20736 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20737 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20738 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20745 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20746 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___198_20774 = rc  in
          let uu____20775 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____20782 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___198_20774.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20775;
            FStar_Syntax_Syntax.residual_flags = uu____20782
          }  in
        let uu____20785 =
          let uu____20786 =
            let uu____20803 = elim_delayed_subst_binders bs  in
            let uu____20810 = elim_delayed_subst_term t2  in
            let uu____20811 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____20803, uu____20810, uu____20811)  in
          FStar_Syntax_Syntax.Tm_abs uu____20786  in
        mk1 uu____20785
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____20840 =
          let uu____20841 =
            let uu____20854 = elim_delayed_subst_binders bs  in
            let uu____20861 = elim_delayed_subst_comp c  in
            (uu____20854, uu____20861)  in
          FStar_Syntax_Syntax.Tm_arrow uu____20841  in
        mk1 uu____20840
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____20874 =
          let uu____20875 =
            let uu____20882 = elim_bv bv  in
            let uu____20883 = elim_delayed_subst_term phi  in
            (uu____20882, uu____20883)  in
          FStar_Syntax_Syntax.Tm_refine uu____20875  in
        mk1 uu____20874
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____20906 =
          let uu____20907 =
            let uu____20922 = elim_delayed_subst_term t2  in
            let uu____20923 = elim_delayed_subst_args args  in
            (uu____20922, uu____20923)  in
          FStar_Syntax_Syntax.Tm_app uu____20907  in
        mk1 uu____20906
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___199_20987 = p  in
              let uu____20988 =
                let uu____20989 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____20989  in
              {
                FStar_Syntax_Syntax.v = uu____20988;
                FStar_Syntax_Syntax.p =
                  (uu___199_20987.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___200_20991 = p  in
              let uu____20992 =
                let uu____20993 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____20993  in
              {
                FStar_Syntax_Syntax.v = uu____20992;
                FStar_Syntax_Syntax.p =
                  (uu___200_20991.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___201_21000 = p  in
              let uu____21001 =
                let uu____21002 =
                  let uu____21009 = elim_bv x  in
                  let uu____21010 = elim_delayed_subst_term t0  in
                  (uu____21009, uu____21010)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____21002  in
              {
                FStar_Syntax_Syntax.v = uu____21001;
                FStar_Syntax_Syntax.p =
                  (uu___201_21000.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___202_21029 = p  in
              let uu____21030 =
                let uu____21031 =
                  let uu____21044 =
                    FStar_List.map
                      (fun uu____21067  ->
                         match uu____21067 with
                         | (x,b) ->
                             let uu____21080 = elim_pat x  in
                             (uu____21080, b)) pats
                     in
                  (fv, uu____21044)  in
                FStar_Syntax_Syntax.Pat_cons uu____21031  in
              {
                FStar_Syntax_Syntax.v = uu____21030;
                FStar_Syntax_Syntax.p =
                  (uu___202_21029.FStar_Syntax_Syntax.p)
              }
          | uu____21093 -> p  in
        let elim_branch uu____21115 =
          match uu____21115 with
          | (pat,wopt,t3) ->
              let uu____21141 = elim_pat pat  in
              let uu____21144 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____21147 = elim_delayed_subst_term t3  in
              (uu____21141, uu____21144, uu____21147)
           in
        let uu____21152 =
          let uu____21153 =
            let uu____21176 = elim_delayed_subst_term t2  in
            let uu____21177 = FStar_List.map elim_branch branches  in
            (uu____21176, uu____21177)  in
          FStar_Syntax_Syntax.Tm_match uu____21153  in
        mk1 uu____21152
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____21286 =
          match uu____21286 with
          | (tc,topt) ->
              let uu____21321 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____21331 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____21331
                | FStar_Util.Inr c ->
                    let uu____21333 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____21333
                 in
              let uu____21334 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____21321, uu____21334)
           in
        let uu____21343 =
          let uu____21344 =
            let uu____21371 = elim_delayed_subst_term t2  in
            let uu____21372 = elim_ascription a  in
            (uu____21371, uu____21372, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____21344  in
        mk1 uu____21343
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___203_21417 = lb  in
          let uu____21418 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____21421 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___203_21417.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___203_21417.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____21418;
            FStar_Syntax_Syntax.lbeff =
              (uu___203_21417.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____21421;
            FStar_Syntax_Syntax.lbattrs =
              (uu___203_21417.FStar_Syntax_Syntax.lbattrs)
          }  in
        let uu____21424 =
          let uu____21425 =
            let uu____21438 =
              let uu____21445 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____21445)  in
            let uu____21454 = elim_delayed_subst_term t2  in
            (uu____21438, uu____21454)  in
          FStar_Syntax_Syntax.Tm_let uu____21425  in
        mk1 uu____21424
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____21487 =
          let uu____21488 =
            let uu____21505 = elim_delayed_subst_term t2  in
            (uv, uu____21505)  in
          FStar_Syntax_Syntax.Tm_uvar uu____21488  in
        mk1 uu____21487
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21522 =
          let uu____21523 =
            let uu____21530 = elim_delayed_subst_term t2  in
            let uu____21531 = elim_delayed_subst_meta md  in
            (uu____21530, uu____21531)  in
          FStar_Syntax_Syntax.Tm_meta uu____21523  in
        mk1 uu____21522

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_21538  ->
         match uu___91_21538 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21542 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____21542
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
        let uu____21563 =
          let uu____21564 =
            let uu____21573 = elim_delayed_subst_term t  in
            (uu____21573, uopt)  in
          FStar_Syntax_Syntax.Total uu____21564  in
        mk1 uu____21563
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21586 =
          let uu____21587 =
            let uu____21596 = elim_delayed_subst_term t  in
            (uu____21596, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____21587  in
        mk1 uu____21586
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___204_21601 = ct  in
          let uu____21602 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____21605 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____21614 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___204_21601.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___204_21601.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21602;
            FStar_Syntax_Syntax.effect_args = uu____21605;
            FStar_Syntax_Syntax.flags = uu____21614
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_21617  ->
    match uu___92_21617 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21629 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____21629
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21662 =
          let uu____21669 = elim_delayed_subst_term t  in (m, uu____21669)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____21662
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21677 =
          let uu____21686 = elim_delayed_subst_term t  in
          (m1, m2, uu____21686)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21677
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21694 =
          let uu____21703 = elim_delayed_subst_term t  in (d, s, uu____21703)
           in
        FStar_Syntax_Syntax.Meta_alien uu____21694
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____21726  ->
         match uu____21726 with
         | (t,q) ->
             let uu____21737 = elim_delayed_subst_term t  in (uu____21737, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21757  ->
         match uu____21757 with
         | (x,q) ->
             let uu____21768 =
               let uu___205_21769 = x  in
               let uu____21770 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___205_21769.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___205_21769.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21770
               }  in
             (uu____21768, q)) bs

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
            | (uu____21846,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____21852,FStar_Util.Inl t) ->
                let uu____21858 =
                  let uu____21861 =
                    let uu____21862 =
                      let uu____21875 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____21875)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____21862  in
                  FStar_Syntax_Syntax.mk uu____21861  in
                uu____21858 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____21879 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____21879 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____21907 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____21962 ->
                    let uu____21963 =
                      let uu____21972 =
                        let uu____21973 = FStar_Syntax_Subst.compress t4  in
                        uu____21973.FStar_Syntax_Syntax.n  in
                      (uu____21972, tc)  in
                    (match uu____21963 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____21998) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____22035) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____22074,FStar_Util.Inl uu____22075) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____22098 -> failwith "Impossible")
                 in
              (match uu____21907 with
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
          let uu____22203 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____22203 with
          | (univ_names1,binders1,tc) ->
              let uu____22261 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____22261)
  
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
          let uu____22296 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____22296 with
          | (univ_names1,binders1,tc) ->
              let uu____22356 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____22356)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____22389 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____22389 with
           | (univ_names1,binders1,typ1) ->
               let uu___206_22417 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_22417.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_22417.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_22417.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_22417.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___207_22438 = s  in
          let uu____22439 =
            let uu____22440 =
              let uu____22449 = FStar_List.map (elim_uvars env) sigs  in
              (uu____22449, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____22440  in
          {
            FStar_Syntax_Syntax.sigel = uu____22439;
            FStar_Syntax_Syntax.sigrng =
              (uu___207_22438.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_22438.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_22438.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_22438.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____22466 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22466 with
           | (univ_names1,uu____22484,typ1) ->
               let uu___208_22498 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_22498.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_22498.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_22498.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_22498.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22504 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22504 with
           | (univ_names1,uu____22522,typ1) ->
               let uu___209_22536 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_22536.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_22536.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_22536.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_22536.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22570 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____22570 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22593 =
                            let uu____22594 =
                              let uu____22595 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____22595  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22594
                             in
                          elim_delayed_subst_term uu____22593  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___210_22598 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___210_22598.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___210_22598.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___210_22598.FStar_Syntax_Syntax.lbattrs)
                        }))
             in
          let uu___211_22599 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___211_22599.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___211_22599.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___211_22599.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___211_22599.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___212_22611 = s  in
          let uu____22612 =
            let uu____22613 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____22613  in
          {
            FStar_Syntax_Syntax.sigel = uu____22612;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_22611.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_22611.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_22611.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_22611.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22617 = elim_uvars_aux_t env us [] t  in
          (match uu____22617 with
           | (us1,uu____22635,t1) ->
               let uu___213_22649 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_22649.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_22649.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_22649.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_22649.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22650 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22652 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____22652 with
           | (univs1,binders,signature) ->
               let uu____22680 =
                 let uu____22689 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____22689 with
                 | (univs_opening,univs2) ->
                     let uu____22716 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____22716)
                  in
               (match uu____22680 with
                | (univs_opening,univs_closing) ->
                    let uu____22733 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____22739 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____22740 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____22739, uu____22740)  in
                    (match uu____22733 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____22762 =
                           match uu____22762 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____22780 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____22780 with
                                | (us1,t1) ->
                                    let uu____22791 =
                                      let uu____22796 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____22803 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____22796, uu____22803)  in
                                    (match uu____22791 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____22816 =
                                           let uu____22821 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____22830 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____22821, uu____22830)  in
                                         (match uu____22816 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____22846 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____22846
                                                 in
                                              let uu____22847 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____22847 with
                                               | (uu____22868,uu____22869,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____22884 =
                                                       let uu____22885 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____22885
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____22884
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____22890 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____22890 with
                           | (uu____22903,uu____22904,t1) -> t1  in
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
                             | uu____22964 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____22981 =
                               let uu____22982 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____22982.FStar_Syntax_Syntax.n  in
                             match uu____22981 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____23041 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____23070 =
                               let uu____23071 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____23071.FStar_Syntax_Syntax.n  in
                             match uu____23070 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____23092) ->
                                 let uu____23113 = destruct_action_body body
                                    in
                                 (match uu____23113 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____23158 ->
                                 let uu____23159 = destruct_action_body t  in
                                 (match uu____23159 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____23208 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____23208 with
                           | (action_univs,t) ->
                               let uu____23217 = destruct_action_typ_templ t
                                  in
                               (match uu____23217 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___214_23258 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___214_23258.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___214_23258.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___215_23260 = ed  in
                           let uu____23261 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____23262 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____23263 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____23264 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____23265 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____23266 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____23267 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____23268 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____23269 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____23270 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____23271 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____23272 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____23273 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____23274 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___215_23260.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___215_23260.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____23261;
                             FStar_Syntax_Syntax.bind_wp = uu____23262;
                             FStar_Syntax_Syntax.if_then_else = uu____23263;
                             FStar_Syntax_Syntax.ite_wp = uu____23264;
                             FStar_Syntax_Syntax.stronger = uu____23265;
                             FStar_Syntax_Syntax.close_wp = uu____23266;
                             FStar_Syntax_Syntax.assert_p = uu____23267;
                             FStar_Syntax_Syntax.assume_p = uu____23268;
                             FStar_Syntax_Syntax.null_wp = uu____23269;
                             FStar_Syntax_Syntax.trivial = uu____23270;
                             FStar_Syntax_Syntax.repr = uu____23271;
                             FStar_Syntax_Syntax.return_repr = uu____23272;
                             FStar_Syntax_Syntax.bind_repr = uu____23273;
                             FStar_Syntax_Syntax.actions = uu____23274
                           }  in
                         let uu___216_23277 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___216_23277.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___216_23277.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___216_23277.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___216_23277.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_23294 =
            match uu___93_23294 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____23321 = elim_uvars_aux_t env us [] t  in
                (match uu____23321 with
                 | (us1,uu____23345,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___217_23364 = sub_eff  in
            let uu____23365 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____23368 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___217_23364.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___217_23364.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____23365;
              FStar_Syntax_Syntax.lift = uu____23368
            }  in
          let uu___218_23371 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___218_23371.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___218_23371.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___218_23371.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___218_23371.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____23381 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____23381 with
           | (univ_names1,binders1,comp1) ->
               let uu___219_23415 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___219_23415.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___219_23415.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___219_23415.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___219_23415.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____23426 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  