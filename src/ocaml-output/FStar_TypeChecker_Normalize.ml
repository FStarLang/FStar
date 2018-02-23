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
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      FStar_Util.psmap_try_find cfg.primitive_steps
        (FStar_Ident.text_of_lid
           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
  
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
    match projectee with | Arg _0 -> true | uu____2049 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2085 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2121 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2190 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2232 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2288 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2328 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2360 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2396 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2412 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____2437 .
    'Auu____2437 ->
      FStar_Range.range -> 'Auu____2437 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2491 = FStar_ST.op_Bang r  in
          match uu____2491 with
          | FStar_Pervasives_Native.Some uu____2539 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2593 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2593 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2600  ->
    match uu___78_2600 with
    | Arg (c,uu____2602,uu____2603) ->
        let uu____2604 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2604
    | MemoLazy uu____2605 -> "MemoLazy"
    | Abs (uu____2612,bs,uu____2614,uu____2615,uu____2616) ->
        let uu____2621 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2621
    | UnivArgs uu____2626 -> "UnivArgs"
    | Match uu____2633 -> "Match"
    | App (uu____2640,t,uu____2642,uu____2643) ->
        let uu____2644 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2644
    | Meta (m,uu____2646) -> "Meta"
    | Let uu____2647 -> "Let"
    | Cfg uu____2656 -> "Cfg"
    | Debug (t,uu____2658) ->
        let uu____2659 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2659
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2667 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2667 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2698 . 'Auu____2698 Prims.list -> Prims.bool =
  fun uu___79_2704  ->
    match uu___79_2704 with | [] -> true | uu____2707 -> false
  
let lookup_bvar :
  'Auu____2714 'Auu____2715 .
    ('Auu____2715,'Auu____2714) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2714
  =
  fun env  ->
    fun x  ->
      try
        let uu____2739 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2739
      with
      | uu____2752 ->
          let uu____2753 =
            let uu____2754 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2754  in
          failwith uu____2753
  
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
          let uu____2791 =
            FStar_List.fold_left
              (fun uu____2817  ->
                 fun u1  ->
                   match uu____2817 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2842 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2842 with
                        | (k_u,n1) ->
                            let uu____2857 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2857
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2791 with
          | (uu____2875,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2900 =
                   let uu____2901 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2901  in
                 match uu____2900 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2919 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2927 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2933 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2942 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2951 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2958 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2958 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2975 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2975 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2983 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2991 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2991 with
                                  | (uu____2996,m) -> n1 <= m))
                           in
                        if uu____2983 then rest1 else us1
                    | uu____3001 -> us1)
               | uu____3006 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3010 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3010
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3014 = aux u  in
           match uu____3014 with
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
          (fun uu____3118  ->
             let uu____3119 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3120 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3119
               uu____3120);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3127 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3129 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3154 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3155 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3156 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3157 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3174 =
                      let uu____3175 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3176 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3175 uu____3176
                       in
                    failwith uu____3174
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3179 =
                    let uu____3180 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3180  in
                  mk uu____3179 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3187 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3187
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3189 = lookup_bvar env x  in
                  (match uu____3189 with
                   | Univ uu____3192 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3195,uu____3196) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3308 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3308 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3336 =
                         let uu____3337 =
                           let uu____3354 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3354)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3337  in
                       mk uu____3336 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3385 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3385 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3427 =
                    let uu____3438 =
                      let uu____3445 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3445]  in
                    closures_as_binders_delayed cfg env uu____3438  in
                  (match uu____3427 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3463 =
                         let uu____3464 =
                           let uu____3471 =
                             let uu____3472 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3472
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3471, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3464  in
                       mk uu____3463 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3563 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3563
                    | FStar_Util.Inr c ->
                        let uu____3577 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3577
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3593 =
                    let uu____3594 =
                      let uu____3621 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3621, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3594  in
                  mk uu____3593 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3672 =
                    let uu____3673 =
                      let uu____3680 = closure_as_term_delayed cfg env t'  in
                      let uu____3683 =
                        let uu____3684 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3684  in
                      (uu____3680, uu____3683)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3673  in
                  mk uu____3672 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3744 =
                    let uu____3745 =
                      let uu____3752 = closure_as_term_delayed cfg env t'  in
                      let uu____3755 =
                        let uu____3756 =
                          let uu____3763 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3763)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3756  in
                      (uu____3752, uu____3755)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3745  in
                  mk uu____3744 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3782 =
                    let uu____3783 =
                      let uu____3790 = closure_as_term_delayed cfg env t'  in
                      let uu____3793 =
                        let uu____3794 =
                          let uu____3803 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3803)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3794  in
                      (uu____3790, uu____3793)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3783  in
                  mk uu____3782 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3816 =
                    let uu____3817 =
                      let uu____3824 = closure_as_term_delayed cfg env t'  in
                      (uu____3824, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3817  in
                  mk uu____3816 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3864  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3883 =
                    let uu____3894 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3894
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3913 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___124_3925 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_3925.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_3925.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3913))
                     in
                  (match uu____3883 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___125_3941 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___125_3941.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___125_3941.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___125_3941.FStar_Syntax_Syntax.lbattrs)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3952,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4011  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4036 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4036
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4056  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4078 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4078
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___126_4090 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_4090.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_4090.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___127_4091 = lb  in
                    let uu____4092 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___127_4091.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___127_4091.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4092;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___127_4091.FStar_Syntax_Syntax.lbattrs)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4122  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4211 =
                    match uu____4211 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4266 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4287 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4347  ->
                                        fun uu____4348  ->
                                          match (uu____4347, uu____4348) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4439 =
                                                norm_pat env3 p1  in
                                              (match uu____4439 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4287 with
                               | (pats1,env3) ->
                                   ((let uu___128_4521 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___128_4521.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___129_4540 = x  in
                                let uu____4541 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4540.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4540.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4541
                                }  in
                              ((let uu___130_4555 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4555.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___131_4566 = x  in
                                let uu____4567 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4566.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4566.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4567
                                }  in
                              ((let uu___132_4581 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4581.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___133_4597 = x  in
                                let uu____4598 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___133_4597.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___133_4597.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4598
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___134_4605 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___134_4605.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4608 = norm_pat env1 pat  in
                        (match uu____4608 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4637 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4637
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4643 =
                    let uu____4644 =
                      let uu____4667 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4667)  in
                    FStar_Syntax_Syntax.Tm_match uu____4644  in
                  mk uu____4643 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4753 -> closure_as_term cfg env t

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
        | uu____4779 ->
            FStar_List.map
              (fun uu____4796  ->
                 match uu____4796 with
                 | (x,imp) ->
                     let uu____4815 = closure_as_term_delayed cfg env x  in
                     (uu____4815, imp)) args

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
        let uu____4829 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4878  ->
                  fun uu____4879  ->
                    match (uu____4878, uu____4879) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___135_4949 = b  in
                          let uu____4950 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___135_4949.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___135_4949.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4950
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4829 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5043 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5056 = closure_as_term_delayed cfg env t  in
                 let uu____5057 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5056 uu____5057
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5070 = closure_as_term_delayed cfg env t  in
                 let uu____5071 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5070 uu____5071
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
                        (fun uu___80_5097  ->
                           match uu___80_5097 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5101 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5101
                           | f -> f))
                    in
                 let uu____5105 =
                   let uu___136_5106 = c1  in
                   let uu____5107 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5107;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___136_5106.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5105)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5117  ->
            match uu___81_5117 with
            | FStar_Syntax_Syntax.DECREASES uu____5118 -> false
            | uu____5121 -> true))

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
                   (fun uu___82_5139  ->
                      match uu___82_5139 with
                      | FStar_Syntax_Syntax.DECREASES uu____5140 -> false
                      | uu____5143 -> true))
               in
            let rc1 =
              let uu___137_5145 = rc  in
              let uu____5146 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___137_5145.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5146;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5153 -> lopt

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
    let uu____5238 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5238  in
  let arg_as_bounded_int uu____5266 =
    match uu____5266 with
    | (a,uu____5278) ->
        let uu____5285 =
          let uu____5286 = FStar_Syntax_Subst.compress a  in
          uu____5286.FStar_Syntax_Syntax.n  in
        (match uu____5285 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5296;
                FStar_Syntax_Syntax.vars = uu____5297;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5299;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5300;_},uu____5301)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5340 =
               let uu____5345 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5345)  in
             FStar_Pervasives_Native.Some uu____5340
         | uu____5350 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5390 = f a  in FStar_Pervasives_Native.Some uu____5390
    | uu____5391 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5439 = f a0 a1  in FStar_Pervasives_Native.Some uu____5439
    | uu____5440 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5482 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5482)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5531 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5531)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5555 =
    match uu____5555 with
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
                   let uu____5603 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5603)) a429 a430)
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
                       let uu____5631 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5631)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5652 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5652)) a436
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
                       let uu____5680 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5680)) a439
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
                       let uu____5708 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5708))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5816 =
          let uu____5825 = as_a a  in
          let uu____5828 = as_b b  in (uu____5825, uu____5828)  in
        (match uu____5816 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5843 =
               let uu____5844 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5844  in
             FStar_Pervasives_Native.Some uu____5843
         | uu____5845 -> FStar_Pervasives_Native.None)
    | uu____5854 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5868 =
        let uu____5869 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5869  in
      mk uu____5868 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5879 =
      let uu____5882 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5882  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5879  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5914 =
      let uu____5915 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5915  in
    FStar_Syntax_Embeddings.embed_int rng uu____5914  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5933 = arg_as_string a1  in
        (match uu____5933 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5939 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5939 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5952 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5952
              | uu____5953 -> FStar_Pervasives_Native.None)
         | uu____5958 -> FStar_Pervasives_Native.None)
    | uu____5961 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5971 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5971  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5995 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6006 =
          let uu____6027 = arg_as_string fn  in
          let uu____6030 = arg_as_int from_line  in
          let uu____6033 = arg_as_int from_col  in
          let uu____6036 = arg_as_int to_line  in
          let uu____6039 = arg_as_int to_col  in
          (uu____6027, uu____6030, uu____6033, uu____6036, uu____6039)  in
        (match uu____6006 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6070 =
                 let uu____6071 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6072 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6071 uu____6072  in
               let uu____6073 =
                 let uu____6074 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6075 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6074 uu____6075  in
               FStar_Range.mk_range fn1 uu____6070 uu____6073  in
             let uu____6076 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____6076
         | uu____6081 -> FStar_Pervasives_Native.None)
    | uu____6102 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6129)::(a1,uu____6131)::(a2,uu____6133)::[] ->
        let uu____6170 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6170 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6183 -> FStar_Pervasives_Native.None)
    | uu____6184 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6211)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6220 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
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
                          let uu____6409 =
                            let uu____6424 =
                              let uu____6439 =
                                let uu____6454 =
                                  let uu____6469 =
                                    let uu____6484 =
                                      let uu____6499 =
                                        let uu____6514 =
                                          let uu____6529 =
                                            let uu____6544 =
                                              let uu____6559 =
                                                let uu____6572 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6572,
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
                                              let uu____6579 =
                                                let uu____6594 =
                                                  let uu____6607 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6607,
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
                                                let uu____6614 =
                                                  let uu____6629 =
                                                    let uu____6644 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6644,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6653 =
                                                    let uu____6670 =
                                                      let uu____6685 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6685,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6694 =
                                                      let uu____6711 =
                                                        let uu____6730 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6730,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6711]  in
                                                    uu____6670 :: uu____6694
                                                     in
                                                  uu____6629 :: uu____6653
                                                   in
                                                uu____6594 :: uu____6614  in
                                              uu____6559 :: uu____6579  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6544
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6529
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
                                          :: uu____6514
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
                                        :: uu____6499
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
                                      :: uu____6484
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
                                                        let uu____6947 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6947 y)) a466
                                                a467 a468)))
                                    :: uu____6469
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6454
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6439
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6424
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6409
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6394
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6379
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
                                          let uu____7114 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7114)) a470 a471 a472)))
                      :: uu____6364
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
                                        let uu____7140 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7140)) a474 a475 a476)))
                    :: uu____6349
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
                                      let uu____7166 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7166)) a478 a479 a480)))
                  :: uu____6334
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
                                    let uu____7192 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7192)) a482 a483 a484)))
                :: uu____6319
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6304
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6289
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6274
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6259
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6244
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7345 =
        let uu____7346 =
          let uu____7347 = FStar_Syntax_Syntax.as_arg c  in [uu____7347]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7346  in
      uu____7345 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7397 =
                let uu____7410 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7410, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7426  ->
                                    fun uu____7427  ->
                                      match (uu____7426, uu____7427) with
                                      | ((int_to_t1,x),(uu____7446,y)) ->
                                          let uu____7456 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7456)) a486 a487 a488)))
                 in
              let uu____7457 =
                let uu____7472 =
                  let uu____7485 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7485, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7501  ->
                                      fun uu____7502  ->
                                        match (uu____7501, uu____7502) with
                                        | ((int_to_t1,x),(uu____7521,y)) ->
                                            let uu____7531 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7531)) a490 a491 a492)))
                   in
                let uu____7532 =
                  let uu____7547 =
                    let uu____7560 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7560, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7576  ->
                                        fun uu____7577  ->
                                          match (uu____7576, uu____7577) with
                                          | ((int_to_t1,x),(uu____7596,y)) ->
                                              let uu____7606 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7606)) a494 a495 a496)))
                     in
                  let uu____7607 =
                    let uu____7622 =
                      let uu____7635 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7635, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7647  ->
                                        match uu____7647 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7622]  in
                  uu____7547 :: uu____7607  in
                uu____7472 :: uu____7532  in
              uu____7397 :: uu____7457))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7761 =
                let uu____7774 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7774, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7790  ->
                                    fun uu____7791  ->
                                      match (uu____7790, uu____7791) with
                                      | ((int_to_t1,x),(uu____7810,y)) ->
                                          let uu____7820 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7820)) a501 a502 a503)))
                 in
              let uu____7821 =
                let uu____7836 =
                  let uu____7849 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7849, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7865  ->
                                      fun uu____7866  ->
                                        match (uu____7865, uu____7866) with
                                        | ((int_to_t1,x),(uu____7885,y)) ->
                                            let uu____7895 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7895)) a505 a506 a507)))
                   in
                [uu____7836]  in
              uu____7761 :: uu____7821))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let uu____7944 =
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  FStar_All.pipe_left prim_from_list uu____7944 
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7992)::(a1,uu____7994)::(a2,uu____7996)::[] ->
        let uu____8033 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8033 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8039 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8039.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8039.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8043 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8043.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8043.FStar_Syntax_Syntax.vars)
                })
         | uu____8044 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8046)::uu____8047::(a1,uu____8049)::(a2,uu____8051)::[] ->
        let uu____8100 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8100 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8106 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8106.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8106.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8110 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8110.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8110.FStar_Syntax_Syntax.vars)
                })
         | uu____8111 -> FStar_Pervasives_Native.None)
    | uu____8112 -> failwith "Unexpected number of arguments"  in
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
      let uu____8131 =
        let uu____8132 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____8132 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____8131
    with | uu____8138 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____8142 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8142) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8202  ->
           fun subst1  ->
             match uu____8202 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8243,uu____8244)) ->
                      let uu____8303 = b  in
                      (match uu____8303 with
                       | (bv,uu____8311) ->
                           let uu____8312 =
                             let uu____8313 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____8313  in
                           if uu____8312
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8318 = unembed_binder term1  in
                              match uu____8318 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8325 =
                                      let uu___142_8326 = bv  in
                                      let uu____8327 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___142_8326.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___142_8326.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8327
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8325
                                     in
                                  let b_for_x =
                                    let uu____8331 =
                                      let uu____8338 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8338)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8331  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8347  ->
                                         match uu___83_8347 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8348,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8350;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8351;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8356 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8357 -> subst1)) env []
  
let reduce_primops :
  'Auu____8374 'Auu____8375 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8375) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8374 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8417 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8417 with
             | (head1,args) ->
                 let uu____8454 =
                   let uu____8455 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8455.FStar_Syntax_Syntax.n  in
                 (match uu____8454 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8459 = find_prim_step cfg fv  in
                      (match uu____8459 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8474  ->
                                   let uu____8475 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8476 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8483 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8475 uu____8476 uu____8483);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8488  ->
                                   let uu____8489 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8489);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8492  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8494 =
                                 prim_step.interpretation psc args  in
                               match uu____8494 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8500  ->
                                         let uu____8501 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8501);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8507  ->
                                         let uu____8508 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8509 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8508 uu____8509);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8510 ->
                           (log_primops cfg
                              (fun uu____8514  ->
                                 let uu____8515 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8515);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8519  ->
                            let uu____8520 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8520);
                       (match args with
                        | (a1,uu____8522)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8539 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8551  ->
                            let uu____8552 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8552);
                       (match args with
                        | (t,uu____8554)::(r,uu____8556)::[] ->
                            let uu____8583 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8583 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___143_8587 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___143_8587.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___143_8587.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8590 -> tm))
                  | uu____8599 -> tm))
  
let reduce_equality :
  'Auu____8604 'Auu____8605 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8605) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8604 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___144_8643 = cfg  in
         {
           steps =
             (let uu___145_8646 = default_steps  in
              {
                beta = (uu___145_8646.beta);
                iota = (uu___145_8646.iota);
                zeta = (uu___145_8646.zeta);
                weak = (uu___145_8646.weak);
                hnf = (uu___145_8646.hnf);
                primops = true;
                eager_unfolding = (uu___145_8646.eager_unfolding);
                inlining = (uu___145_8646.inlining);
                no_delta_steps = (uu___145_8646.no_delta_steps);
                unfold_until = (uu___145_8646.unfold_until);
                unfold_only = (uu___145_8646.unfold_only);
                unfold_attr = (uu___145_8646.unfold_attr);
                unfold_tac = (uu___145_8646.unfold_tac);
                pure_subterms_within_computations =
                  (uu___145_8646.pure_subterms_within_computations);
                simplify = (uu___145_8646.simplify);
                erase_universes = (uu___145_8646.erase_universes);
                allow_unbound_universes =
                  (uu___145_8646.allow_unbound_universes);
                reify_ = (uu___145_8646.reify_);
                compress_uvars = (uu___145_8646.compress_uvars);
                no_full_norm = (uu___145_8646.no_full_norm);
                check_no_uvars = (uu___145_8646.check_no_uvars);
                unmeta = (uu___145_8646.unmeta);
                unascribe = (uu___145_8646.unascribe)
              });
           tcenv = (uu___144_8643.tcenv);
           debug = (uu___144_8643.debug);
           delta_level = (uu___144_8643.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___144_8643.strong);
           memoize_lazy = (uu___144_8643.memoize_lazy);
           normalize_pure_lets = (uu___144_8643.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8653 'Auu____8654 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8654) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8653 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8696 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8696
          then tm1
          else
            (let w t =
               let uu___146_8708 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___146_8708.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___146_8708.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8724;
                      FStar_Syntax_Syntax.vars = uu____8725;_},uu____8726)
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
                      FStar_Syntax_Syntax.pos = uu____8733;
                      FStar_Syntax_Syntax.vars = uu____8734;_},uu____8735)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8741 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8746 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8746
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8767 =
                 match uu____8767 with
                 | (t1,q) ->
                     let uu____8780 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8780 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8808 -> (t1, q))
                  in
               let uu____8817 = FStar_Syntax_Util.head_and_args t  in
               match uu____8817 with
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
                         FStar_Syntax_Syntax.pos = uu____8914;
                         FStar_Syntax_Syntax.vars = uu____8915;_},uu____8916);
                    FStar_Syntax_Syntax.pos = uu____8917;
                    FStar_Syntax_Syntax.vars = uu____8918;_},args)
                 ->
                 let uu____8944 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8944
                 then
                   let uu____8945 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8945 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9000)::
                        (uu____9001,(arg,uu____9003))::[] ->
                        maybe_auto_squash arg
                    | (uu____9068,(arg,uu____9070))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9071)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9136)::uu____9137::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9200::(FStar_Pervasives_Native.Some (false
                                   ),uu____9201)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9264 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9280 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9280
                    then
                      let uu____9281 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9281 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9336)::uu____9337::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9400::(FStar_Pervasives_Native.Some (true
                                     ),uu____9401)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9464)::
                          (uu____9465,(arg,uu____9467))::[] ->
                          maybe_auto_squash arg
                      | (uu____9532,(arg,uu____9534))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9535)::[]
                          -> maybe_auto_squash arg
                      | uu____9600 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9616 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9616
                       then
                         let uu____9617 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9617 with
                         | uu____9672::(FStar_Pervasives_Native.Some (true
                                        ),uu____9673)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9736)::uu____9737::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9800)::
                             (uu____9801,(arg,uu____9803))::[] ->
                             maybe_auto_squash arg
                         | (uu____9868,(p,uu____9870))::(uu____9871,(q,uu____9873))::[]
                             ->
                             let uu____9938 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9938
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9940 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9956 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9956
                          then
                            let uu____9957 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9957 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10012)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10051)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10090 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10106 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10106
                             then
                               match args with
                               | (t,uu____10108)::[] ->
                                   let uu____10125 =
                                     let uu____10126 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10126.FStar_Syntax_Syntax.n  in
                                   (match uu____10125 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10129::[],body,uu____10131) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10158 -> tm1)
                                    | uu____10161 -> tm1)
                               | (uu____10162,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10163))::
                                   (t,uu____10165)::[] ->
                                   let uu____10204 =
                                     let uu____10205 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10205.FStar_Syntax_Syntax.n  in
                                   (match uu____10204 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10208::[],body,uu____10210) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10237 -> tm1)
                                    | uu____10240 -> tm1)
                               | uu____10241 -> tm1
                             else
                               (let uu____10251 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10251
                                then
                                  match args with
                                  | (t,uu____10253)::[] ->
                                      let uu____10270 =
                                        let uu____10271 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10271.FStar_Syntax_Syntax.n  in
                                      (match uu____10270 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10274::[],body,uu____10276)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10303 -> tm1)
                                       | uu____10306 -> tm1)
                                  | (uu____10307,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10308))::(t,uu____10310)::[] ->
                                      let uu____10349 =
                                        let uu____10350 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10350.FStar_Syntax_Syntax.n  in
                                      (match uu____10349 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10353::[],body,uu____10355)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10382 -> tm1)
                                       | uu____10385 -> tm1)
                                  | uu____10386 -> tm1
                                else
                                  (let uu____10396 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10396
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10397;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10398;_},uu____10399)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10416;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10417;_},uu____10418)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10435 -> tm1
                                   else
                                     (let uu____10445 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10445 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10465 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10475;
                    FStar_Syntax_Syntax.vars = uu____10476;_},args)
                 ->
                 let uu____10498 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____10498
                 then
                   let uu____10499 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____10499 with
                    | (FStar_Pervasives_Native.Some (true ),uu____10554)::
                        (uu____10555,(arg,uu____10557))::[] ->
                        maybe_auto_squash arg
                    | (uu____10622,(arg,uu____10624))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____10625)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____10690)::uu____10691::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10754::(FStar_Pervasives_Native.Some (false
                                    ),uu____10755)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10818 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____10834 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____10834
                    then
                      let uu____10835 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____10835 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10890)::uu____10891::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10954::(FStar_Pervasives_Native.Some (true
                                      ),uu____10955)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11018)::
                          (uu____11019,(arg,uu____11021))::[] ->
                          maybe_auto_squash arg
                      | (uu____11086,(arg,uu____11088))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11089)::[]
                          -> maybe_auto_squash arg
                      | uu____11154 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11170 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11170
                       then
                         let uu____11171 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11171 with
                         | uu____11226::(FStar_Pervasives_Native.Some (true
                                         ),uu____11227)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11290)::uu____11291::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11354)::
                             (uu____11355,(arg,uu____11357))::[] ->
                             maybe_auto_squash arg
                         | (uu____11422,(p,uu____11424))::(uu____11425,
                                                           (q,uu____11427))::[]
                             ->
                             let uu____11492 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____11492
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11494 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____11510 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____11510
                          then
                            let uu____11511 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____11511 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____11566)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____11605)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____11644 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____11660 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____11660
                             then
                               match args with
                               | (t,uu____11662)::[] ->
                                   let uu____11679 =
                                     let uu____11680 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11680.FStar_Syntax_Syntax.n  in
                                   (match uu____11679 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11683::[],body,uu____11685) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11712 -> tm1)
                                    | uu____11715 -> tm1)
                               | (uu____11716,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____11717))::
                                   (t,uu____11719)::[] ->
                                   let uu____11758 =
                                     let uu____11759 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11759.FStar_Syntax_Syntax.n  in
                                   (match uu____11758 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11762::[],body,uu____11764) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11791 -> tm1)
                                    | uu____11794 -> tm1)
                               | uu____11795 -> tm1
                             else
                               (let uu____11805 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____11805
                                then
                                  match args with
                                  | (t,uu____11807)::[] ->
                                      let uu____11824 =
                                        let uu____11825 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11825.FStar_Syntax_Syntax.n  in
                                      (match uu____11824 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11828::[],body,uu____11830)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11857 -> tm1)
                                       | uu____11860 -> tm1)
                                  | (uu____11861,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____11862))::(t,uu____11864)::[] ->
                                      let uu____11903 =
                                        let uu____11904 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11904.FStar_Syntax_Syntax.n  in
                                      (match uu____11903 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11907::[],body,uu____11909)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11936 -> tm1)
                                       | uu____11939 -> tm1)
                                  | uu____11940 -> tm1
                                else
                                  (let uu____11950 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____11950
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11951;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11952;_},uu____11953)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11970;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11971;_},uu____11972)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11989 -> tm1
                                   else
                                     (let uu____11999 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____11999 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____12019 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____12034 -> tm1)
  
let maybe_simplify :
  'Auu____12041 'Auu____12042 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____12042) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____12041 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____12085 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12086 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____12085
               uu____12086)
          else ();
          tm'
  
let is_norm_request :
  'Auu____12092 .
    FStar_Syntax_Syntax.term -> 'Auu____12092 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____12105 =
        let uu____12112 =
          let uu____12113 = FStar_Syntax_Util.un_uinst hd1  in
          uu____12113.FStar_Syntax_Syntax.n  in
        (uu____12112, args)  in
      match uu____12105 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12119::uu____12120::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12124::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____12129::uu____12130::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____12133 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_12144  ->
    match uu___84_12144 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12150 =
          let uu____12153 =
            let uu____12154 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____12154  in
          [uu____12153]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____12150
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12170 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____12170) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____12223 =
            let uu____12226 =
              let uu____12229 =
                let uu____12234 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____12234 s  in
              FStar_All.pipe_right uu____12229 FStar_Util.must  in
            FStar_All.pipe_right uu____12226 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____12223
        with | uu____12262 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____12273::(tm,uu____12275)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____12304)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____12325)::uu____12326::(tm,uu____12328)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let uu____12365 =
            let uu____12370 = full_norm steps  in parse_steps uu____12370  in
          (match uu____12365 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____12409 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_12426  ->
    match uu___85_12426 with
    | (App
        (uu____12429,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12430;
                       FStar_Syntax_Syntax.vars = uu____12431;_},uu____12432,uu____12433))::uu____12434
        -> true
    | uu____12441 -> false
  
let firstn :
  'Auu____12447 .
    Prims.int ->
      'Auu____12447 Prims.list ->
        ('Auu____12447 Prims.list,'Auu____12447 Prims.list)
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
          (uu____12483,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12484;
                         FStar_Syntax_Syntax.vars = uu____12485;_},uu____12486,uu____12487))::uu____12488
          -> (cfg.steps).reify_
      | uu____12495 -> false
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let r =
        let uu____12505 = FStar_Syntax_Util.eq_tm a a'  in
        match uu____12505 with
        | FStar_Syntax_Util.Equal  -> true
        | uu____12506 -> false  in
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12648 ->
                   let uu____12673 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12673
               | uu____12674 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12682  ->
               let uu____12683 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12684 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12685 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12692 =
                 let uu____12693 =
                   let uu____12696 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12696
                    in
                 stack_to_string uu____12693  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12683 uu____12684 uu____12685 uu____12692);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12719 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12720 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12721;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12722;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12725;
                 FStar_Syntax_Syntax.fv_delta = uu____12726;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12727;
                 FStar_Syntax_Syntax.fv_delta = uu____12728;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12729);_}
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
                 let uu___149_12771 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___149_12771.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___149_12771.FStar_Syntax_Syntax.vars)
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
                 let uu___150_12809 = cfg  in
                 {
                   steps =
                     (let uu___151_12812 = cfg.steps  in
                      {
                        beta = (uu___151_12812.beta);
                        iota = (uu___151_12812.iota);
                        zeta = (uu___151_12812.zeta);
                        weak = (uu___151_12812.weak);
                        hnf = (uu___151_12812.hnf);
                        primops = (uu___151_12812.primops);
                        eager_unfolding = (uu___151_12812.eager_unfolding);
                        inlining = (uu___151_12812.inlining);
                        no_delta_steps = false;
                        unfold_until = (uu___151_12812.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___151_12812.unfold_attr);
                        unfold_tac = (uu___151_12812.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___151_12812.pure_subterms_within_computations);
                        simplify = (uu___151_12812.simplify);
                        erase_universes = (uu___151_12812.erase_universes);
                        allow_unbound_universes =
                          (uu___151_12812.allow_unbound_universes);
                        reify_ = (uu___151_12812.reify_);
                        compress_uvars = (uu___151_12812.compress_uvars);
                        no_full_norm = (uu___151_12812.no_full_norm);
                        check_no_uvars = (uu___151_12812.check_no_uvars);
                        unmeta = (uu___151_12812.unmeta);
                        unascribe = (uu___151_12812.unascribe)
                      });
                   tcenv = (uu___150_12809.tcenv);
                   debug = (uu___150_12809.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___150_12809.primitive_steps);
                   strong = (uu___150_12809.strong);
                   memoize_lazy = (uu___150_12809.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12815 = get_norm_request (norm cfg' env []) args  in
               (match uu____12815 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12846  ->
                              fun stack1  ->
                                match uu____12846 with
                                | (a,aq) ->
                                    let uu____12858 =
                                      let uu____12859 =
                                        let uu____12866 =
                                          let uu____12867 =
                                            let uu____12898 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12898, false)  in
                                          Clos uu____12867  in
                                        (uu____12866, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12859  in
                                    uu____12858 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12982  ->
                          let uu____12983 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12983);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____13005 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_13010  ->
                                match uu___86_13010 with
                                | UnfoldUntil uu____13011 -> true
                                | UnfoldOnly uu____13012 -> true
                                | uu____13015 -> false))
                         in
                      if uu____13005
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___152_13020 = cfg  in
                      let uu____13021 = to_fsteps s  in
                      {
                        steps = uu____13021;
                        tcenv = (uu___152_13020.tcenv);
                        debug = (uu___152_13020.debug);
                        delta_level;
                        primitive_steps = (uu___152_13020.primitive_steps);
                        strong = (uu___152_13020.strong);
                        memoize_lazy = (uu___152_13020.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____13030 =
                          let uu____13031 =
                            let uu____13036 = FStar_Util.now ()  in
                            (t1, uu____13036)  in
                          Debug uu____13031  in
                        uu____13030 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____13040 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13040
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____13049 =
                      let uu____13056 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____13056, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____13049  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____13066 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____13066  in
               let uu____13067 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____13067
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____13073  ->
                       let uu____13074 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13075 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____13074 uu____13075);
                  if b
                  then
                    (let uu____13076 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____13076 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____13084 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____13084) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___87_13090  ->
                               match uu___87_13090 with
                               | FStar_TypeChecker_Env.UnfoldTac  -> false
                               | FStar_TypeChecker_Env.NoDelta  -> false
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | FStar_TypeChecker_Env.Unfold l ->
                                   FStar_TypeChecker_Common.delta_depth_greater_than
                                     fv.FStar_Syntax_Syntax.fv_delta l)))
                     in
                  let should_delta1 =
                    if Prims.op_Negation should_delta
                    then false
                    else
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____13100 =
                             cases
                               (FStar_Util.for_some
                                  (attr_eq FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____13100))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____13119) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some (attr_eq at) ats')
                                   ats
                             | (uu____13154,uu____13155) -> false)))
                     in
                  log cfg
                    (fun uu____13177  ->
                       let uu____13178 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13179 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13180 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____13178
                         uu____13179 uu____13180);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____13183 = lookup_bvar env x  in
               (match uu____13183 with
                | Univ uu____13186 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____13235 = FStar_ST.op_Bang r  in
                      (match uu____13235 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____13353  ->
                                 let uu____13354 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____13355 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____13354
                                   uu____13355);
                            (let uu____13356 =
                               let uu____13357 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____13357.FStar_Syntax_Syntax.n  in
                             match uu____13356 with
                             | FStar_Syntax_Syntax.Tm_abs uu____13360 ->
                                 norm cfg env2 stack t'
                             | uu____13377 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13447)::uu____13448 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____13457)::uu____13458 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____13468,uu____13469))::stack_rest ->
                    (match c with
                     | Univ uu____13473 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13482 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13503  ->
                                    let uu____13504 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13504);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13544  ->
                                    let uu____13545 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13545);
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
                       (fun uu____13623  ->
                          let uu____13624 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13624);
                     norm cfg env stack1 t1)
                | (Debug uu____13625)::uu____13626 ->
                    if (cfg.steps).weak
                    then
                      let uu____13633 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13633
                    else
                      (let uu____13635 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13635 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13677  -> dummy :: env1) env)
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
                                          let uu____13714 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13714)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_13719 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_13719.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_13719.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13720 -> lopt  in
                           (log cfg
                              (fun uu____13726  ->
                                 let uu____13727 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13727);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_13736 = cfg  in
                               {
                                 steps = (uu___154_13736.steps);
                                 tcenv = (uu___154_13736.tcenv);
                                 debug = (uu___154_13736.debug);
                                 delta_level = (uu___154_13736.delta_level);
                                 primitive_steps =
                                   (uu___154_13736.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_13736.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_13736.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13747)::uu____13748 ->
                    if (cfg.steps).weak
                    then
                      let uu____13755 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13755
                    else
                      (let uu____13757 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13757 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13799  -> dummy :: env1) env)
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
                                          let uu____13836 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13836)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_13841 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_13841.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_13841.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13842 -> lopt  in
                           (log cfg
                              (fun uu____13848  ->
                                 let uu____13849 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13849);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_13858 = cfg  in
                               {
                                 steps = (uu___154_13858.steps);
                                 tcenv = (uu___154_13858.tcenv);
                                 debug = (uu___154_13858.debug);
                                 delta_level = (uu___154_13858.delta_level);
                                 primitive_steps =
                                   (uu___154_13858.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_13858.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_13858.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13869)::uu____13870 ->
                    if (cfg.steps).weak
                    then
                      let uu____13881 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13881
                    else
                      (let uu____13883 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13883 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13925  -> dummy :: env1) env)
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
                                          let uu____13962 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13962)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_13967 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_13967.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_13967.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13968 -> lopt  in
                           (log cfg
                              (fun uu____13974  ->
                                 let uu____13975 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13975);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_13984 = cfg  in
                               {
                                 steps = (uu___154_13984.steps);
                                 tcenv = (uu___154_13984.tcenv);
                                 debug = (uu___154_13984.debug);
                                 delta_level = (uu___154_13984.delta_level);
                                 primitive_steps =
                                   (uu___154_13984.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_13984.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_13984.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13995)::uu____13996 ->
                    if (cfg.steps).weak
                    then
                      let uu____14007 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14007
                    else
                      (let uu____14009 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14009 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14051  -> dummy :: env1) env)
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
                                          let uu____14088 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14088)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_14093 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_14093.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_14093.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14094 -> lopt  in
                           (log cfg
                              (fun uu____14100  ->
                                 let uu____14101 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14101);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_14110 = cfg  in
                               {
                                 steps = (uu___154_14110.steps);
                                 tcenv = (uu___154_14110.tcenv);
                                 debug = (uu___154_14110.debug);
                                 delta_level = (uu___154_14110.delta_level);
                                 primitive_steps =
                                   (uu___154_14110.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_14110.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_14110.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____14121)::uu____14122 ->
                    if (cfg.steps).weak
                    then
                      let uu____14137 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14137
                    else
                      (let uu____14139 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14139 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14181  -> dummy :: env1) env)
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
                                          let uu____14218 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14218)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_14223 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_14223.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_14223.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14224 -> lopt  in
                           (log cfg
                              (fun uu____14230  ->
                                 let uu____14231 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14231);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_14240 = cfg  in
                               {
                                 steps = (uu___154_14240.steps);
                                 tcenv = (uu___154_14240.tcenv);
                                 debug = (uu___154_14240.debug);
                                 delta_level = (uu___154_14240.delta_level);
                                 primitive_steps =
                                   (uu___154_14240.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_14240.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_14240.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____14251 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14251
                    else
                      (let uu____14253 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14253 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14295  -> dummy :: env1) env)
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
                                          let uu____14332 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14332)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___153_14337 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___153_14337.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___153_14337.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14338 -> lopt  in
                           (log cfg
                              (fun uu____14344  ->
                                 let uu____14345 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14345);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___154_14354 = cfg  in
                               {
                                 steps = (uu___154_14354.steps);
                                 tcenv = (uu___154_14354.tcenv);
                                 debug = (uu___154_14354.debug);
                                 delta_level = (uu___154_14354.delta_level);
                                 primitive_steps =
                                   (uu___154_14354.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___154_14354.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_14354.normalize_pure_lets)
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
                      (fun uu____14403  ->
                         fun stack1  ->
                           match uu____14403 with
                           | (a,aq) ->
                               let uu____14415 =
                                 let uu____14416 =
                                   let uu____14423 =
                                     let uu____14424 =
                                       let uu____14455 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____14455, false)  in
                                     Clos uu____14424  in
                                   (uu____14423, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____14416  in
                               uu____14415 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14539  ->
                     let uu____14540 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14540);
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
                             ((let uu___155_14576 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_14576.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_14576.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14577 ->
                      let uu____14582 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14582)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14585 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14585 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14616 =
                          let uu____14617 =
                            let uu____14624 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___156_14626 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___156_14626.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___156_14626.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14624)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14617  in
                        mk uu____14616 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14645 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14645
               else
                 (let uu____14647 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14647 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14655 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14679  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14655 c1  in
                      let t2 =
                        let uu____14701 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14701 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14812)::uu____14813 ->
                    (log cfg
                       (fun uu____14824  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14825)::uu____14826 ->
                    (log cfg
                       (fun uu____14837  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14838,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14839;
                                   FStar_Syntax_Syntax.vars = uu____14840;_},uu____14841,uu____14842))::uu____14843
                    ->
                    (log cfg
                       (fun uu____14852  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14853)::uu____14854 ->
                    (log cfg
                       (fun uu____14865  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14866 ->
                    (log cfg
                       (fun uu____14869  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14873  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14890 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14890
                         | FStar_Util.Inr c ->
                             let uu____14898 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14898
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14911 =
                               let uu____14912 =
                                 let uu____14939 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14939, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14912
                                in
                             mk uu____14911 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14958 ->
                           let uu____14959 =
                             let uu____14960 =
                               let uu____14961 =
                                 let uu____14988 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14988, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14961
                                in
                             mk uu____14960 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14959))))
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
                         let uu____15098 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____15098 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___157_15118 = cfg  in
                               let uu____15119 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___157_15118.steps);
                                 tcenv = uu____15119;
                                 debug = (uu___157_15118.debug);
                                 delta_level = (uu___157_15118.delta_level);
                                 primitive_steps =
                                   (uu___157_15118.primitive_steps);
                                 strong = (uu___157_15118.strong);
                                 memoize_lazy = (uu___157_15118.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___157_15118.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____15124 =
                                 let uu____15125 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____15125  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____15124
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___158_15128 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___158_15128.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___158_15128.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___158_15128.FStar_Syntax_Syntax.lbattrs)
                             }))
                  in
               let uu____15129 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____15129
           | FStar_Syntax_Syntax.Tm_let
               ((uu____15140,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____15141;
                               FStar_Syntax_Syntax.lbunivs = uu____15142;
                               FStar_Syntax_Syntax.lbtyp = uu____15143;
                               FStar_Syntax_Syntax.lbeff = uu____15144;
                               FStar_Syntax_Syntax.lbdef = uu____15145;
                               FStar_Syntax_Syntax.lbattrs = uu____15146;_}::uu____15147),uu____15148)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____15188 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____15188
               then
                 let binder =
                   let uu____15190 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____15190  in
                 let env1 =
                   let uu____15200 =
                     let uu____15207 =
                       let uu____15208 =
                         let uu____15239 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____15239,
                           false)
                          in
                       Clos uu____15208  in
                     ((FStar_Pervasives_Native.Some binder), uu____15207)  in
                   uu____15200 :: env  in
                 (log cfg
                    (fun uu____15332  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____15336  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____15337 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____15337))
                 else
                   (let uu____15339 =
                      let uu____15344 =
                        let uu____15345 =
                          let uu____15346 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____15346
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____15345]  in
                      FStar_Syntax_Subst.open_term uu____15344 body  in
                    match uu____15339 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____15355  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____15363 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____15363  in
                            FStar_Util.Inl
                              (let uu___159_15373 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_15373.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_15373.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____15376  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___160_15378 = lb  in
                             let uu____15379 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___160_15378.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___160_15378.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15379;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___160_15378.FStar_Syntax_Syntax.lbattrs)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15414  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___161_15437 = cfg  in
                             {
                               steps = (uu___161_15437.steps);
                               tcenv = (uu___161_15437.tcenv);
                               debug = (uu___161_15437.debug);
                               delta_level = (uu___161_15437.delta_level);
                               primitive_steps =
                                 (uu___161_15437.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___161_15437.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___161_15437.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15440  ->
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
               let uu____15457 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15457 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15493 =
                               let uu___162_15494 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___162_15494.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___162_15494.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15493  in
                           let uu____15495 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15495 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15521 =
                                   FStar_List.map (fun uu____15537  -> dummy)
                                     lbs1
                                    in
                                 let uu____15538 =
                                   let uu____15547 =
                                     FStar_List.map
                                       (fun uu____15567  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15547 env  in
                                 FStar_List.append uu____15521 uu____15538
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15591 =
                                       let uu___163_15592 = rc  in
                                       let uu____15593 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___163_15592.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15593;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___163_15592.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15591
                                 | uu____15600 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___164_15604 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___164_15604.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___164_15604.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___164_15604.FStar_Syntax_Syntax.lbattrs)
                               }) lbs1
                       in
                    let env' =
                      let uu____15614 =
                        FStar_List.map (fun uu____15630  -> dummy) lbs2  in
                      FStar_List.append uu____15614 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15638 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15638 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___165_15654 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___165_15654.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___165_15654.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15681 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15681
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15700 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15776  ->
                        match uu____15776 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___166_15897 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_15897.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___166_15897.FStar_Syntax_Syntax.sort)
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
               (match uu____15700 with
                | (rec_env,memos,uu____16110) ->
                    let uu____16163 =
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
                             let uu____16474 =
                               let uu____16481 =
                                 let uu____16482 =
                                   let uu____16513 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16513, false)
                                    in
                                 Clos uu____16482  in
                               (FStar_Pervasives_Native.None, uu____16481)
                                in
                             uu____16474 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16623  ->
                     let uu____16624 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16624);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16646 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16648::uu____16649 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16654) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16655 ->
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
                             | uu____16686 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16700 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16700
                              | uu____16711 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16715 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16741 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16759 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16776 =
                        let uu____16777 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16778 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16777 uu____16778
                         in
                      failwith uu____16776
                    else rebuild cfg env stack t2
                | uu____16780 -> norm cfg env stack t2))

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
                let uu____16790 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16790  in
              let uu____16791 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16791 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16804  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16815  ->
                        let uu____16816 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16817 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16816 uu____16817);
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
                      | (UnivArgs (us',uu____16830))::stack1 ->
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
                      | uu____16885 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____16888 ->
                          let uu____16891 =
                            let uu____16892 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16892
                             in
                          failwith uu____16891
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
                  let uu___167_16913 = cfg  in
                  let uu____16914 =
                    to_fsteps
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      Inlining]
                     in
                  {
                    steps = uu____16914;
                    tcenv = (uu___167_16913.tcenv);
                    debug = (uu___167_16913.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___167_16913.primitive_steps);
                    strong = (uu___167_16913.strong);
                    memoize_lazy = (uu___167_16913.memoize_lazy);
                    normalize_pure_lets =
                      (uu___167_16913.normalize_pure_lets)
                  }
                else
                  (let uu___168_16916 = cfg  in
                   {
                     steps =
                       (let uu___169_16919 = cfg.steps  in
                        {
                          beta = (uu___169_16919.beta);
                          iota = (uu___169_16919.iota);
                          zeta = false;
                          weak = (uu___169_16919.weak);
                          hnf = (uu___169_16919.hnf);
                          primops = (uu___169_16919.primops);
                          eager_unfolding = (uu___169_16919.eager_unfolding);
                          inlining = (uu___169_16919.inlining);
                          no_delta_steps = (uu___169_16919.no_delta_steps);
                          unfold_until = (uu___169_16919.unfold_until);
                          unfold_only = (uu___169_16919.unfold_only);
                          unfold_attr = (uu___169_16919.unfold_attr);
                          unfold_tac = (uu___169_16919.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___169_16919.pure_subterms_within_computations);
                          simplify = (uu___169_16919.simplify);
                          erase_universes = (uu___169_16919.erase_universes);
                          allow_unbound_universes =
                            (uu___169_16919.allow_unbound_universes);
                          reify_ = (uu___169_16919.reify_);
                          compress_uvars = (uu___169_16919.compress_uvars);
                          no_full_norm = (uu___169_16919.no_full_norm);
                          check_no_uvars = (uu___169_16919.check_no_uvars);
                          unmeta = (uu___169_16919.unmeta);
                          unascribe = (uu___169_16919.unascribe)
                        });
                     tcenv = (uu___168_16916.tcenv);
                     debug = (uu___168_16916.debug);
                     delta_level = (uu___168_16916.delta_level);
                     primitive_steps = (uu___168_16916.primitive_steps);
                     strong = (uu___168_16916.strong);
                     memoize_lazy = (uu___168_16916.memoize_lazy);
                     normalize_pure_lets =
                       (uu___168_16916.normalize_pure_lets)
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
                  (fun uu____16949  ->
                     let uu____16950 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16951 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16950
                       uu____16951);
                (let uu____16952 =
                   let uu____16953 = FStar_Syntax_Subst.compress head2  in
                   uu____16953.FStar_Syntax_Syntax.n  in
                 match uu____16952 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16971 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16971 with
                      | (uu____16972,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16978 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16986 =
                                   let uu____16987 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16987.FStar_Syntax_Syntax.n  in
                                 match uu____16986 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16993,uu____16994))
                                     ->
                                     let uu____17003 =
                                       let uu____17004 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____17004.FStar_Syntax_Syntax.n  in
                                     (match uu____17003 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____17010,msrc,uu____17012))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____17021 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____17021
                                      | uu____17022 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____17023 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____17024 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____17024 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___170_17029 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___170_17029.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___170_17029.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___170_17029.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___170_17029.FStar_Syntax_Syntax.lbattrs)
                                      }  in
                                    let uu____17030 = FStar_List.tl stack  in
                                    let uu____17031 =
                                      let uu____17032 =
                                        let uu____17035 =
                                          let uu____17036 =
                                            let uu____17049 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____17049)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____17036
                                           in
                                        FStar_Syntax_Syntax.mk uu____17035
                                         in
                                      uu____17032
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____17030 uu____17031
                                | FStar_Pervasives_Native.None  ->
                                    let uu____17065 =
                                      let uu____17066 = is_return body  in
                                      match uu____17066 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____17070;
                                            FStar_Syntax_Syntax.vars =
                                              uu____17071;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____17076 -> false  in
                                    if uu____17065
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
                                         let uu____17099 =
                                           let uu____17102 =
                                             let uu____17103 =
                                               let uu____17120 =
                                                 let uu____17123 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____17123]  in
                                               (uu____17120, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____17103
                                              in
                                           FStar_Syntax_Syntax.mk uu____17102
                                            in
                                         uu____17099
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____17139 =
                                           let uu____17140 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____17140.FStar_Syntax_Syntax.n
                                            in
                                         match uu____17139 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____17146::uu____17147::[])
                                             ->
                                             let uu____17154 =
                                               let uu____17157 =
                                                 let uu____17158 =
                                                   let uu____17165 =
                                                     let uu____17168 =
                                                       let uu____17169 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____17169
                                                        in
                                                     let uu____17170 =
                                                       let uu____17173 =
                                                         let uu____17174 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____17174
                                                          in
                                                       [uu____17173]  in
                                                     uu____17168 ::
                                                       uu____17170
                                                      in
                                                   (bind1, uu____17165)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____17158
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____17157
                                                in
                                             uu____17154
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____17182 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____17188 =
                                           let uu____17191 =
                                             let uu____17192 =
                                               let uu____17207 =
                                                 let uu____17210 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____17211 =
                                                   let uu____17214 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____17215 =
                                                     let uu____17218 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____17219 =
                                                       let uu____17222 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____17223 =
                                                         let uu____17226 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____17227 =
                                                           let uu____17230 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____17230]  in
                                                         uu____17226 ::
                                                           uu____17227
                                                          in
                                                       uu____17222 ::
                                                         uu____17223
                                                        in
                                                     uu____17218 ::
                                                       uu____17219
                                                      in
                                                   uu____17214 :: uu____17215
                                                    in
                                                 uu____17210 :: uu____17211
                                                  in
                                               (bind_inst, uu____17207)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____17192
                                              in
                                           FStar_Syntax_Syntax.mk uu____17191
                                            in
                                         uu____17188
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____17242  ->
                                            let uu____17243 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____17244 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____17243 uu____17244);
                                       (let uu____17245 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____17245 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____17269 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17269 with
                      | (uu____17270,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17305 =
                                  let uu____17306 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____17306.FStar_Syntax_Syntax.n  in
                                match uu____17305 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17312) -> t2
                                | uu____17317 -> head3  in
                              let uu____17318 =
                                let uu____17319 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17319.FStar_Syntax_Syntax.n  in
                              match uu____17318 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17325 -> FStar_Pervasives_Native.None
                               in
                            let uu____17326 = maybe_extract_fv head3  in
                            match uu____17326 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17336 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17336
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____17341 = maybe_extract_fv head4
                                     in
                                  match uu____17341 with
                                  | FStar_Pervasives_Native.Some uu____17346
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17347 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____17352 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17367 =
                              match uu____17367 with
                              | (e,q) ->
                                  let uu____17374 =
                                    let uu____17375 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17375.FStar_Syntax_Syntax.n  in
                                  (match uu____17374 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____17390 -> false)
                               in
                            let uu____17391 =
                              let uu____17392 =
                                let uu____17399 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17399 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17392
                               in
                            if uu____17391
                            then
                              let uu____17404 =
                                let uu____17405 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17405
                                 in
                              failwith uu____17404
                            else ());
                           (let uu____17407 = maybe_unfold_action head_app
                               in
                            match uu____17407 with
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
                                   (fun uu____17448  ->
                                      let uu____17449 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17450 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17449 uu____17450);
                                 (let uu____17451 = FStar_List.tl stack  in
                                  norm cfg env uu____17451 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17453) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17477 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17477  in
                     (log cfg
                        (fun uu____17481  ->
                           let uu____17482 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17482);
                      (let uu____17483 = FStar_List.tl stack  in
                       norm cfg env uu____17483 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____17485) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17610  ->
                               match uu____17610 with
                               | (pat,wopt,tm) ->
                                   let uu____17658 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17658)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____17690 = FStar_List.tl stack  in
                     norm cfg env uu____17690 tm
                 | uu____17691 -> fallback ())

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
              (fun uu____17705  ->
                 let uu____17706 = FStar_Ident.string_of_lid msrc  in
                 let uu____17707 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17708 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17706
                   uu____17707 uu____17708);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____17710 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17710 with
               | (uu____17711,return_repr) ->
                   let return_inst =
                     let uu____17720 =
                       let uu____17721 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17721.FStar_Syntax_Syntax.n  in
                     match uu____17720 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17727::[]) ->
                         let uu____17734 =
                           let uu____17737 =
                             let uu____17738 =
                               let uu____17745 =
                                 let uu____17748 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17748]  in
                               (return_tm, uu____17745)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17738  in
                           FStar_Syntax_Syntax.mk uu____17737  in
                         uu____17734 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17756 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17759 =
                     let uu____17762 =
                       let uu____17763 =
                         let uu____17778 =
                           let uu____17781 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17782 =
                             let uu____17785 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17785]  in
                           uu____17781 :: uu____17782  in
                         (return_inst, uu____17778)  in
                       FStar_Syntax_Syntax.Tm_app uu____17763  in
                     FStar_Syntax_Syntax.mk uu____17762  in
                   uu____17759 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17794 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17794 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17797 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17797
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17798;
                     FStar_TypeChecker_Env.mtarget = uu____17799;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17800;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17815 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17815
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17816;
                     FStar_TypeChecker_Env.mtarget = uu____17817;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17818;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17842 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17843 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17842 t FStar_Syntax_Syntax.tun uu____17843)

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
                (fun uu____17899  ->
                   match uu____17899 with
                   | (a,imp) ->
                       let uu____17910 = norm cfg env [] a  in
                       (uu____17910, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___171_17924 = comp  in
            let uu____17925 =
              let uu____17926 =
                let uu____17935 = norm cfg env [] t  in
                let uu____17936 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17935, uu____17936)  in
              FStar_Syntax_Syntax.Total uu____17926  in
            {
              FStar_Syntax_Syntax.n = uu____17925;
              FStar_Syntax_Syntax.pos =
                (uu___171_17924.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___171_17924.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___172_17951 = comp  in
            let uu____17952 =
              let uu____17953 =
                let uu____17962 = norm cfg env [] t  in
                let uu____17963 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17962, uu____17963)  in
              FStar_Syntax_Syntax.GTotal uu____17953  in
            {
              FStar_Syntax_Syntax.n = uu____17952;
              FStar_Syntax_Syntax.pos =
                (uu___172_17951.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___172_17951.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____18015  ->
                      match uu____18015 with
                      | (a,i) ->
                          let uu____18026 = norm cfg env [] a  in
                          (uu____18026, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_18037  ->
                      match uu___88_18037 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____18041 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____18041
                      | f -> f))
               in
            let uu___173_18045 = comp  in
            let uu____18046 =
              let uu____18047 =
                let uu___174_18048 = ct  in
                let uu____18049 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____18050 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____18053 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____18049;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___174_18048.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____18050;
                  FStar_Syntax_Syntax.effect_args = uu____18053;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____18047  in
            {
              FStar_Syntax_Syntax.n = uu____18046;
              FStar_Syntax_Syntax.pos =
                (uu___173_18045.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_18045.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____18064  ->
        match uu____18064 with
        | (x,imp) ->
            let uu____18067 =
              let uu___175_18068 = x  in
              let uu____18069 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___175_18068.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___175_18068.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18069
              }  in
            (uu____18067, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18075 =
          FStar_List.fold_left
            (fun uu____18093  ->
               fun b  ->
                 match uu____18093 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18075 with | (nbs,uu____18133) -> FStar_List.rev nbs

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
            let uu____18149 =
              let uu___176_18150 = rc  in
              let uu____18151 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___176_18150.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18151;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___176_18150.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18149
        | uu____18158 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____18171  ->
               let uu____18172 = FStar_Syntax_Print.tag_of_term t  in
               let uu____18173 = FStar_Syntax_Print.term_to_string t  in
               let uu____18174 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____18181 =
                 let uu____18182 =
                   let uu____18185 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____18185
                    in
                 stack_to_string uu____18182  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____18172 uu____18173 uu____18174 uu____18181);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____18216 =
                     let uu____18217 =
                       let uu____18218 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____18218  in
                     FStar_Util.string_of_int uu____18217  in
                   let uu____18223 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____18224 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____18216 uu____18223 uu____18224)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____18278  ->
                     let uu____18279 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____18279);
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
               let uu____18315 =
                 let uu___177_18316 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___177_18316.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___177_18316.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____18315
           | (Arg (Univ uu____18317,uu____18318,uu____18319))::uu____18320 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____18323,uu____18324))::uu____18325 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____18341),aq,r))::stack1 ->
               (log cfg
                  (fun uu____18394  ->
                     let uu____18395 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____18395);
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
                  (let uu____18405 = FStar_ST.op_Bang m  in
                   match uu____18405 with
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
                   | FStar_Pervasives_Native.Some (uu____18542,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____18589 =
                 log cfg
                   (fun uu____18593  ->
                      let uu____18594 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18594);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____18598 =
                 let uu____18599 = FStar_Syntax_Subst.compress t1  in
                 uu____18599.FStar_Syntax_Syntax.n  in
               (match uu____18598 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18626 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____18626  in
                    (log cfg
                       (fun uu____18630  ->
                          let uu____18631 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18631);
                     (let uu____18632 = FStar_List.tl stack  in
                      norm cfg env1 uu____18632 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18633);
                       FStar_Syntax_Syntax.pos = uu____18634;
                       FStar_Syntax_Syntax.vars = uu____18635;_},(e,uu____18637)::[])
                    -> norm cfg env1 stack' e
                | uu____18666 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18686  ->
                     let uu____18687 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18687);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____18692 =
                   log cfg
                     (fun uu____18697  ->
                        let uu____18698 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____18699 =
                          let uu____18700 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18717  ->
                                    match uu____18717 with
                                    | (p,uu____18727,uu____18728) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____18700
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18698 uu____18699);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_18745  ->
                                match uu___89_18745 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18746 -> false))
                         in
                      let uu___178_18747 = cfg  in
                      {
                        steps =
                          (let uu___179_18750 = cfg.steps  in
                           {
                             beta = (uu___179_18750.beta);
                             iota = (uu___179_18750.iota);
                             zeta = false;
                             weak = (uu___179_18750.weak);
                             hnf = (uu___179_18750.hnf);
                             primops = (uu___179_18750.primops);
                             eager_unfolding =
                               (uu___179_18750.eager_unfolding);
                             inlining = (uu___179_18750.inlining);
                             no_delta_steps = (uu___179_18750.no_delta_steps);
                             unfold_until = (uu___179_18750.unfold_until);
                             unfold_only = (uu___179_18750.unfold_only);
                             unfold_attr = (uu___179_18750.unfold_attr);
                             unfold_tac = (uu___179_18750.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___179_18750.pure_subterms_within_computations);
                             simplify = (uu___179_18750.simplify);
                             erase_universes =
                               (uu___179_18750.erase_universes);
                             allow_unbound_universes =
                               (uu___179_18750.allow_unbound_universes);
                             reify_ = (uu___179_18750.reify_);
                             compress_uvars = (uu___179_18750.compress_uvars);
                             no_full_norm = (uu___179_18750.no_full_norm);
                             check_no_uvars = (uu___179_18750.check_no_uvars);
                             unmeta = (uu___179_18750.unmeta);
                             unascribe = (uu___179_18750.unascribe)
                           });
                        tcenv = (uu___178_18747.tcenv);
                        debug = (uu___178_18747.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___178_18747.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___178_18747.memoize_lazy);
                        normalize_pure_lets =
                          (uu___178_18747.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18782 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18803 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18863  ->
                                    fun uu____18864  ->
                                      match (uu____18863, uu____18864) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18955 = norm_pat env3 p1
                                             in
                                          (match uu____18955 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____18803 with
                           | (pats1,env3) ->
                               ((let uu___180_19037 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___180_19037.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___181_19056 = x  in
                            let uu____19057 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_19056.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_19056.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____19057
                            }  in
                          ((let uu___182_19071 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_19071.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___183_19082 = x  in
                            let uu____19083 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_19082.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_19082.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____19083
                            }  in
                          ((let uu___184_19097 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___184_19097.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___185_19113 = x  in
                            let uu____19114 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___185_19113.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___185_19113.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____19114
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___186_19121 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___186_19121.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____19131 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____19145 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____19145 with
                                  | (p,wopt,e) ->
                                      let uu____19165 = norm_pat env1 p  in
                                      (match uu____19165 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____19190 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____19190
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____19196 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____19196)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____19206) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____19211 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____19212;
                         FStar_Syntax_Syntax.fv_delta = uu____19213;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____19214;
                         FStar_Syntax_Syntax.fv_delta = uu____19215;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____19216);_}
                       -> true
                   | uu____19223 -> false  in
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
                   let uu____19368 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____19368 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____19455 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19494 ->
                                 let uu____19495 =
                                   let uu____19496 = is_cons head1  in
                                   Prims.op_Negation uu____19496  in
                                 FStar_Util.Inr uu____19495)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19521 =
                              let uu____19522 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____19522.FStar_Syntax_Syntax.n  in
                            (match uu____19521 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19540 ->
                                 let uu____19541 =
                                   let uu____19542 = is_cons head1  in
                                   Prims.op_Negation uu____19542  in
                                 FStar_Util.Inr uu____19541))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19611)::rest_a,(p1,uu____19614)::rest_p) ->
                       let uu____19658 = matches_pat t2 p1  in
                       (match uu____19658 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19707 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19813 = matches_pat scrutinee1 p1  in
                       (match uu____19813 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19853  ->
                                  let uu____19854 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____19855 =
                                    let uu____19856 =
                                      FStar_List.map
                                        (fun uu____19866  ->
                                           match uu____19866 with
                                           | (uu____19871,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____19856
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19854 uu____19855);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19902  ->
                                       match uu____19902 with
                                       | (bv,t2) ->
                                           let uu____19925 =
                                             let uu____19932 =
                                               let uu____19935 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____19935
                                                in
                                             let uu____19936 =
                                               let uu____19937 =
                                                 let uu____19968 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____19968, false)
                                                  in
                                               Clos uu____19937  in
                                             (uu____19932, uu____19936)  in
                                           uu____19925 :: env2) env1 s
                                 in
                              let uu____20085 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____20085)))
                    in
                 if Prims.op_Negation (cfg.steps).iota
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____20108 =
      let uu____20111 = FStar_ST.op_Bang plugins  in p :: uu____20111  in
    FStar_ST.op_Colon_Equals plugins uu____20108  in
  let retrieve uu____20209 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____20274  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___90_20307  ->
                  match uu___90_20307 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____20311 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____20317 -> d  in
        let uu____20320 = to_fsteps s  in
        let uu____20321 =
          let uu____20322 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____20323 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____20324 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____20325 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____20326 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____20322;
            primop = uu____20323;
            b380 = uu____20324;
            norm_delayed = uu____20325;
            print_normalized = uu____20326
          }  in
        let uu____20327 =
          let uu____20330 =
            let uu____20333 = retrieve_plugins ()  in
            FStar_List.append uu____20333 psteps  in
          add_steps built_in_primitive_steps uu____20330  in
        let uu____20336 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____20338 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____20338)
           in
        {
          steps = uu____20320;
          tcenv = e;
          debug = uu____20321;
          delta_level = d1;
          primitive_steps = uu____20327;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____20336
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
      fun t  -> let uu____20396 = config s e  in norm_comp uu____20396 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____20409 = config [] env  in norm_universe uu____20409 [] u
  
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
        let uu____20427 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____20427  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____20434 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___187_20453 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___187_20453.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___187_20453.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____20460 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____20460
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
                  let uu___188_20469 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___188_20469.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___188_20469.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___188_20469.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___189_20471 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___189_20471.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___189_20471.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___189_20471.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___189_20471.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___190_20472 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___190_20472.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___190_20472.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____20474 -> c
  
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
        let uu____20486 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____20486  in
      let uu____20493 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____20493
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____20497  ->
                 let uu____20498 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____20498)
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
            ((let uu____20515 =
                let uu____20520 =
                  let uu____20521 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____20521
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____20520)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____20515);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____20532 = config [AllowUnboundUniverses] env  in
          norm_comp uu____20532 [] c
        with
        | e ->
            ((let uu____20545 =
                let uu____20550 =
                  let uu____20551 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____20551
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____20550)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____20545);
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
                   let uu____20588 =
                     let uu____20589 =
                       let uu____20596 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____20596)  in
                     FStar_Syntax_Syntax.Tm_refine uu____20589  in
                   mk uu____20588 t01.FStar_Syntax_Syntax.pos
               | uu____20601 -> t2)
          | uu____20602 -> t2  in
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
        let uu____20642 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____20642 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____20671 ->
                 let uu____20678 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____20678 with
                  | (actuals,uu____20688,uu____20689) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____20703 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____20703 with
                         | (binders,args) ->
                             let uu____20720 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____20720
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
      | uu____20728 ->
          let uu____20729 = FStar_Syntax_Util.head_and_args t  in
          (match uu____20729 with
           | (head1,args) ->
               let uu____20766 =
                 let uu____20767 = FStar_Syntax_Subst.compress head1  in
                 uu____20767.FStar_Syntax_Syntax.n  in
               (match uu____20766 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20770,thead) ->
                    let uu____20796 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____20796 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20838 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___195_20846 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___195_20846.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___195_20846.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___195_20846.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___195_20846.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___195_20846.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___195_20846.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___195_20846.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___195_20846.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___195_20846.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___195_20846.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___195_20846.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___195_20846.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___195_20846.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___195_20846.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___195_20846.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___195_20846.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___195_20846.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___195_20846.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___195_20846.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___195_20846.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___195_20846.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___195_20846.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___195_20846.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___195_20846.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___195_20846.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___195_20846.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___195_20846.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___195_20846.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___195_20846.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___195_20846.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___195_20846.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___195_20846.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____20838 with
                            | (uu____20847,ty,uu____20849) ->
                                eta_expand_with_type env t ty))
                | uu____20850 ->
                    let uu____20851 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___196_20859 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___196_20859.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___196_20859.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___196_20859.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___196_20859.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___196_20859.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___196_20859.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___196_20859.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___196_20859.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___196_20859.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___196_20859.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___196_20859.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___196_20859.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___196_20859.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___196_20859.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___196_20859.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___196_20859.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___196_20859.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___196_20859.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___196_20859.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___196_20859.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___196_20859.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___196_20859.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___196_20859.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___196_20859.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___196_20859.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___196_20859.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___196_20859.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___196_20859.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___196_20859.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___196_20859.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___196_20859.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___196_20859.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____20851 with
                     | (uu____20860,ty,uu____20862) ->
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
      let uu___197_20919 = x  in
      let uu____20920 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___197_20919.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___197_20919.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20920
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20923 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20948 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20949 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20950 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20951 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20958 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20959 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___198_20987 = rc  in
          let uu____20988 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____20995 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___198_20987.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20988;
            FStar_Syntax_Syntax.residual_flags = uu____20995
          }  in
        let uu____20998 =
          let uu____20999 =
            let uu____21016 = elim_delayed_subst_binders bs  in
            let uu____21023 = elim_delayed_subst_term t2  in
            let uu____21024 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____21016, uu____21023, uu____21024)  in
          FStar_Syntax_Syntax.Tm_abs uu____20999  in
        mk1 uu____20998
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____21053 =
          let uu____21054 =
            let uu____21067 = elim_delayed_subst_binders bs  in
            let uu____21074 = elim_delayed_subst_comp c  in
            (uu____21067, uu____21074)  in
          FStar_Syntax_Syntax.Tm_arrow uu____21054  in
        mk1 uu____21053
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____21087 =
          let uu____21088 =
            let uu____21095 = elim_bv bv  in
            let uu____21096 = elim_delayed_subst_term phi  in
            (uu____21095, uu____21096)  in
          FStar_Syntax_Syntax.Tm_refine uu____21088  in
        mk1 uu____21087
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____21119 =
          let uu____21120 =
            let uu____21135 = elim_delayed_subst_term t2  in
            let uu____21136 = elim_delayed_subst_args args  in
            (uu____21135, uu____21136)  in
          FStar_Syntax_Syntax.Tm_app uu____21120  in
        mk1 uu____21119
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___199_21200 = p  in
              let uu____21201 =
                let uu____21202 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____21202  in
              {
                FStar_Syntax_Syntax.v = uu____21201;
                FStar_Syntax_Syntax.p =
                  (uu___199_21200.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___200_21204 = p  in
              let uu____21205 =
                let uu____21206 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____21206  in
              {
                FStar_Syntax_Syntax.v = uu____21205;
                FStar_Syntax_Syntax.p =
                  (uu___200_21204.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___201_21213 = p  in
              let uu____21214 =
                let uu____21215 =
                  let uu____21222 = elim_bv x  in
                  let uu____21223 = elim_delayed_subst_term t0  in
                  (uu____21222, uu____21223)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____21215  in
              {
                FStar_Syntax_Syntax.v = uu____21214;
                FStar_Syntax_Syntax.p =
                  (uu___201_21213.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___202_21242 = p  in
              let uu____21243 =
                let uu____21244 =
                  let uu____21257 =
                    FStar_List.map
                      (fun uu____21280  ->
                         match uu____21280 with
                         | (x,b) ->
                             let uu____21293 = elim_pat x  in
                             (uu____21293, b)) pats
                     in
                  (fv, uu____21257)  in
                FStar_Syntax_Syntax.Pat_cons uu____21244  in
              {
                FStar_Syntax_Syntax.v = uu____21243;
                FStar_Syntax_Syntax.p =
                  (uu___202_21242.FStar_Syntax_Syntax.p)
              }
          | uu____21306 -> p  in
        let elim_branch uu____21328 =
          match uu____21328 with
          | (pat,wopt,t3) ->
              let uu____21354 = elim_pat pat  in
              let uu____21357 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____21360 = elim_delayed_subst_term t3  in
              (uu____21354, uu____21357, uu____21360)
           in
        let uu____21365 =
          let uu____21366 =
            let uu____21389 = elim_delayed_subst_term t2  in
            let uu____21390 = FStar_List.map elim_branch branches  in
            (uu____21389, uu____21390)  in
          FStar_Syntax_Syntax.Tm_match uu____21366  in
        mk1 uu____21365
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____21499 =
          match uu____21499 with
          | (tc,topt) ->
              let uu____21534 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____21544 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____21544
                | FStar_Util.Inr c ->
                    let uu____21546 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____21546
                 in
              let uu____21547 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____21534, uu____21547)
           in
        let uu____21556 =
          let uu____21557 =
            let uu____21584 = elim_delayed_subst_term t2  in
            let uu____21585 = elim_ascription a  in
            (uu____21584, uu____21585, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____21557  in
        mk1 uu____21556
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___203_21630 = lb  in
          let uu____21631 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____21634 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___203_21630.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___203_21630.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____21631;
            FStar_Syntax_Syntax.lbeff =
              (uu___203_21630.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____21634;
            FStar_Syntax_Syntax.lbattrs =
              (uu___203_21630.FStar_Syntax_Syntax.lbattrs)
          }  in
        let uu____21637 =
          let uu____21638 =
            let uu____21651 =
              let uu____21658 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____21658)  in
            let uu____21667 = elim_delayed_subst_term t2  in
            (uu____21651, uu____21667)  in
          FStar_Syntax_Syntax.Tm_let uu____21638  in
        mk1 uu____21637
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____21700 =
          let uu____21701 =
            let uu____21718 = elim_delayed_subst_term t2  in
            (uv, uu____21718)  in
          FStar_Syntax_Syntax.Tm_uvar uu____21701  in
        mk1 uu____21700
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21735 =
          let uu____21736 =
            let uu____21743 = elim_delayed_subst_term t2  in
            let uu____21744 = elim_delayed_subst_meta md  in
            (uu____21743, uu____21744)  in
          FStar_Syntax_Syntax.Tm_meta uu____21736  in
        mk1 uu____21735

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_21751  ->
         match uu___91_21751 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21755 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____21755
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
        let uu____21776 =
          let uu____21777 =
            let uu____21786 = elim_delayed_subst_term t  in
            (uu____21786, uopt)  in
          FStar_Syntax_Syntax.Total uu____21777  in
        mk1 uu____21776
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21799 =
          let uu____21800 =
            let uu____21809 = elim_delayed_subst_term t  in
            (uu____21809, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____21800  in
        mk1 uu____21799
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___204_21814 = ct  in
          let uu____21815 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____21818 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____21827 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___204_21814.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___204_21814.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21815;
            FStar_Syntax_Syntax.effect_args = uu____21818;
            FStar_Syntax_Syntax.flags = uu____21827
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_21830  ->
    match uu___92_21830 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21842 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____21842
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21875 =
          let uu____21882 = elim_delayed_subst_term t  in (m, uu____21882)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____21875
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21890 =
          let uu____21899 = elim_delayed_subst_term t  in
          (m1, m2, uu____21899)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21890
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21907 =
          let uu____21916 = elim_delayed_subst_term t  in (d, s, uu____21916)
           in
        FStar_Syntax_Syntax.Meta_alien uu____21907
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____21939  ->
         match uu____21939 with
         | (t,q) ->
             let uu____21950 = elim_delayed_subst_term t  in (uu____21950, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21970  ->
         match uu____21970 with
         | (x,q) ->
             let uu____21981 =
               let uu___205_21982 = x  in
               let uu____21983 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___205_21982.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___205_21982.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21983
               }  in
             (uu____21981, q)) bs

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
            | (uu____22059,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____22065,FStar_Util.Inl t) ->
                let uu____22071 =
                  let uu____22074 =
                    let uu____22075 =
                      let uu____22088 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____22088)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____22075  in
                  FStar_Syntax_Syntax.mk uu____22074  in
                uu____22071 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____22092 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____22092 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____22120 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____22175 ->
                    let uu____22176 =
                      let uu____22185 =
                        let uu____22186 = FStar_Syntax_Subst.compress t4  in
                        uu____22186.FStar_Syntax_Syntax.n  in
                      (uu____22185, tc)  in
                    (match uu____22176 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____22211) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____22248) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____22287,FStar_Util.Inl uu____22288) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____22311 -> failwith "Impossible")
                 in
              (match uu____22120 with
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
          let uu____22416 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____22416 with
          | (univ_names1,binders1,tc) ->
              let uu____22474 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____22474)
  
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
          let uu____22509 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____22509 with
          | (univ_names1,binders1,tc) ->
              let uu____22569 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____22569)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____22602 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____22602 with
           | (univ_names1,binders1,typ1) ->
               let uu___206_22630 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_22630.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_22630.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_22630.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_22630.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___207_22651 = s  in
          let uu____22652 =
            let uu____22653 =
              let uu____22662 = FStar_List.map (elim_uvars env) sigs  in
              (uu____22662, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____22653  in
          {
            FStar_Syntax_Syntax.sigel = uu____22652;
            FStar_Syntax_Syntax.sigrng =
              (uu___207_22651.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_22651.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_22651.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_22651.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____22679 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22679 with
           | (univ_names1,uu____22697,typ1) ->
               let uu___208_22711 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_22711.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_22711.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_22711.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_22711.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22717 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22717 with
           | (univ_names1,uu____22735,typ1) ->
               let uu___209_22749 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_22749.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_22749.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_22749.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_22749.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22783 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____22783 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22806 =
                            let uu____22807 =
                              let uu____22808 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____22808  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22807
                             in
                          elim_delayed_subst_term uu____22806  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___210_22811 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___210_22811.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___210_22811.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___210_22811.FStar_Syntax_Syntax.lbattrs)
                        }))
             in
          let uu___211_22812 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___211_22812.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___211_22812.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___211_22812.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___211_22812.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___212_22824 = s  in
          let uu____22825 =
            let uu____22826 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____22826  in
          {
            FStar_Syntax_Syntax.sigel = uu____22825;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_22824.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_22824.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_22824.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_22824.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22830 = elim_uvars_aux_t env us [] t  in
          (match uu____22830 with
           | (us1,uu____22848,t1) ->
               let uu___213_22862 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_22862.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_22862.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_22862.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_22862.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22863 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22865 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____22865 with
           | (univs1,binders,signature) ->
               let uu____22893 =
                 let uu____22902 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____22902 with
                 | (univs_opening,univs2) ->
                     let uu____22929 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____22929)
                  in
               (match uu____22893 with
                | (univs_opening,univs_closing) ->
                    let uu____22946 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____22952 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____22953 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____22952, uu____22953)  in
                    (match uu____22946 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____22975 =
                           match uu____22975 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____22993 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____22993 with
                                | (us1,t1) ->
                                    let uu____23004 =
                                      let uu____23009 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____23016 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____23009, uu____23016)  in
                                    (match uu____23004 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____23029 =
                                           let uu____23034 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____23043 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____23034, uu____23043)  in
                                         (match uu____23029 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____23059 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____23059
                                                 in
                                              let uu____23060 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____23060 with
                                               | (uu____23081,uu____23082,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____23097 =
                                                       let uu____23098 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____23098
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____23097
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____23103 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____23103 with
                           | (uu____23116,uu____23117,t1) -> t1  in
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
                             | uu____23177 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____23194 =
                               let uu____23195 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____23195.FStar_Syntax_Syntax.n  in
                             match uu____23194 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____23254 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____23283 =
                               let uu____23284 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____23284.FStar_Syntax_Syntax.n  in
                             match uu____23283 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____23305) ->
                                 let uu____23326 = destruct_action_body body
                                    in
                                 (match uu____23326 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____23371 ->
                                 let uu____23372 = destruct_action_body t  in
                                 (match uu____23372 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____23421 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____23421 with
                           | (action_univs,t) ->
                               let uu____23430 = destruct_action_typ_templ t
                                  in
                               (match uu____23430 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___214_23471 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___214_23471.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___214_23471.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___215_23473 = ed  in
                           let uu____23474 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____23475 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____23476 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____23477 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____23478 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____23479 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____23480 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____23481 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____23482 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____23483 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____23484 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____23485 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____23486 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____23487 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___215_23473.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___215_23473.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____23474;
                             FStar_Syntax_Syntax.bind_wp = uu____23475;
                             FStar_Syntax_Syntax.if_then_else = uu____23476;
                             FStar_Syntax_Syntax.ite_wp = uu____23477;
                             FStar_Syntax_Syntax.stronger = uu____23478;
                             FStar_Syntax_Syntax.close_wp = uu____23479;
                             FStar_Syntax_Syntax.assert_p = uu____23480;
                             FStar_Syntax_Syntax.assume_p = uu____23481;
                             FStar_Syntax_Syntax.null_wp = uu____23482;
                             FStar_Syntax_Syntax.trivial = uu____23483;
                             FStar_Syntax_Syntax.repr = uu____23484;
                             FStar_Syntax_Syntax.return_repr = uu____23485;
                             FStar_Syntax_Syntax.bind_repr = uu____23486;
                             FStar_Syntax_Syntax.actions = uu____23487
                           }  in
                         let uu___216_23490 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___216_23490.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___216_23490.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___216_23490.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___216_23490.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_23507 =
            match uu___93_23507 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____23534 = elim_uvars_aux_t env us [] t  in
                (match uu____23534 with
                 | (us1,uu____23558,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___217_23577 = sub_eff  in
            let uu____23578 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____23581 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___217_23577.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___217_23577.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____23578;
              FStar_Syntax_Syntax.lift = uu____23581
            }  in
          let uu___218_23584 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___218_23584.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___218_23584.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___218_23584.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___218_23584.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____23594 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____23594 with
           | (univ_names1,binders1,comp1) ->
               let uu___219_23628 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___219_23628.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___219_23628.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___219_23628.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___219_23628.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____23639 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  