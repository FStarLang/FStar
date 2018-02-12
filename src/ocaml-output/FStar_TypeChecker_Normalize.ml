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
      fun uu___73_180  ->
        match uu___73_180 with
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
          let uu___91_1100 = fs  in
          {
            beta = true;
            iota = (uu___91_1100.iota);
            zeta = (uu___91_1100.zeta);
            weak = (uu___91_1100.weak);
            hnf = (uu___91_1100.hnf);
            primops = (uu___91_1100.primops);
            eager_unfolding = (uu___91_1100.eager_unfolding);
            inlining = (uu___91_1100.inlining);
            no_delta_steps = (uu___91_1100.no_delta_steps);
            unfold_until = (uu___91_1100.unfold_until);
            unfold_only = (uu___91_1100.unfold_only);
            unfold_attr = (uu___91_1100.unfold_attr);
            unfold_tac = (uu___91_1100.unfold_tac);
            pure_subterms_within_computations =
              (uu___91_1100.pure_subterms_within_computations);
            simplify = (uu___91_1100.simplify);
            erase_universes = (uu___91_1100.erase_universes);
            allow_unbound_universes = (uu___91_1100.allow_unbound_universes);
            reify_ = (uu___91_1100.reify_);
            compress_uvars = (uu___91_1100.compress_uvars);
            no_full_norm = (uu___91_1100.no_full_norm);
            check_no_uvars = (uu___91_1100.check_no_uvars);
            unmeta = (uu___91_1100.unmeta);
            unascribe = (uu___91_1100.unascribe)
          }
      | Iota  ->
          let uu___92_1101 = fs  in
          {
            beta = (uu___92_1101.beta);
            iota = true;
            zeta = (uu___92_1101.zeta);
            weak = (uu___92_1101.weak);
            hnf = (uu___92_1101.hnf);
            primops = (uu___92_1101.primops);
            eager_unfolding = (uu___92_1101.eager_unfolding);
            inlining = (uu___92_1101.inlining);
            no_delta_steps = (uu___92_1101.no_delta_steps);
            unfold_until = (uu___92_1101.unfold_until);
            unfold_only = (uu___92_1101.unfold_only);
            unfold_attr = (uu___92_1101.unfold_attr);
            unfold_tac = (uu___92_1101.unfold_tac);
            pure_subterms_within_computations =
              (uu___92_1101.pure_subterms_within_computations);
            simplify = (uu___92_1101.simplify);
            erase_universes = (uu___92_1101.erase_universes);
            allow_unbound_universes = (uu___92_1101.allow_unbound_universes);
            reify_ = (uu___92_1101.reify_);
            compress_uvars = (uu___92_1101.compress_uvars);
            no_full_norm = (uu___92_1101.no_full_norm);
            check_no_uvars = (uu___92_1101.check_no_uvars);
            unmeta = (uu___92_1101.unmeta);
            unascribe = (uu___92_1101.unascribe)
          }
      | Zeta  ->
          let uu___93_1102 = fs  in
          {
            beta = (uu___93_1102.beta);
            iota = (uu___93_1102.iota);
            zeta = true;
            weak = (uu___93_1102.weak);
            hnf = (uu___93_1102.hnf);
            primops = (uu___93_1102.primops);
            eager_unfolding = (uu___93_1102.eager_unfolding);
            inlining = (uu___93_1102.inlining);
            no_delta_steps = (uu___93_1102.no_delta_steps);
            unfold_until = (uu___93_1102.unfold_until);
            unfold_only = (uu___93_1102.unfold_only);
            unfold_attr = (uu___93_1102.unfold_attr);
            unfold_tac = (uu___93_1102.unfold_tac);
            pure_subterms_within_computations =
              (uu___93_1102.pure_subterms_within_computations);
            simplify = (uu___93_1102.simplify);
            erase_universes = (uu___93_1102.erase_universes);
            allow_unbound_universes = (uu___93_1102.allow_unbound_universes);
            reify_ = (uu___93_1102.reify_);
            compress_uvars = (uu___93_1102.compress_uvars);
            no_full_norm = (uu___93_1102.no_full_norm);
            check_no_uvars = (uu___93_1102.check_no_uvars);
            unmeta = (uu___93_1102.unmeta);
            unascribe = (uu___93_1102.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___94_1103 = fs  in
          {
            beta = false;
            iota = (uu___94_1103.iota);
            zeta = (uu___94_1103.zeta);
            weak = (uu___94_1103.weak);
            hnf = (uu___94_1103.hnf);
            primops = (uu___94_1103.primops);
            eager_unfolding = (uu___94_1103.eager_unfolding);
            inlining = (uu___94_1103.inlining);
            no_delta_steps = (uu___94_1103.no_delta_steps);
            unfold_until = (uu___94_1103.unfold_until);
            unfold_only = (uu___94_1103.unfold_only);
            unfold_attr = (uu___94_1103.unfold_attr);
            unfold_tac = (uu___94_1103.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1103.pure_subterms_within_computations);
            simplify = (uu___94_1103.simplify);
            erase_universes = (uu___94_1103.erase_universes);
            allow_unbound_universes = (uu___94_1103.allow_unbound_universes);
            reify_ = (uu___94_1103.reify_);
            compress_uvars = (uu___94_1103.compress_uvars);
            no_full_norm = (uu___94_1103.no_full_norm);
            check_no_uvars = (uu___94_1103.check_no_uvars);
            unmeta = (uu___94_1103.unmeta);
            unascribe = (uu___94_1103.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___95_1104 = fs  in
          {
            beta = (uu___95_1104.beta);
            iota = false;
            zeta = (uu___95_1104.zeta);
            weak = (uu___95_1104.weak);
            hnf = (uu___95_1104.hnf);
            primops = (uu___95_1104.primops);
            eager_unfolding = (uu___95_1104.eager_unfolding);
            inlining = (uu___95_1104.inlining);
            no_delta_steps = (uu___95_1104.no_delta_steps);
            unfold_until = (uu___95_1104.unfold_until);
            unfold_only = (uu___95_1104.unfold_only);
            unfold_attr = (uu___95_1104.unfold_attr);
            unfold_tac = (uu___95_1104.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1104.pure_subterms_within_computations);
            simplify = (uu___95_1104.simplify);
            erase_universes = (uu___95_1104.erase_universes);
            allow_unbound_universes = (uu___95_1104.allow_unbound_universes);
            reify_ = (uu___95_1104.reify_);
            compress_uvars = (uu___95_1104.compress_uvars);
            no_full_norm = (uu___95_1104.no_full_norm);
            check_no_uvars = (uu___95_1104.check_no_uvars);
            unmeta = (uu___95_1104.unmeta);
            unascribe = (uu___95_1104.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___96_1105 = fs  in
          {
            beta = (uu___96_1105.beta);
            iota = (uu___96_1105.iota);
            zeta = false;
            weak = (uu___96_1105.weak);
            hnf = (uu___96_1105.hnf);
            primops = (uu___96_1105.primops);
            eager_unfolding = (uu___96_1105.eager_unfolding);
            inlining = (uu___96_1105.inlining);
            no_delta_steps = (uu___96_1105.no_delta_steps);
            unfold_until = (uu___96_1105.unfold_until);
            unfold_only = (uu___96_1105.unfold_only);
            unfold_attr = (uu___96_1105.unfold_attr);
            unfold_tac = (uu___96_1105.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1105.pure_subterms_within_computations);
            simplify = (uu___96_1105.simplify);
            erase_universes = (uu___96_1105.erase_universes);
            allow_unbound_universes = (uu___96_1105.allow_unbound_universes);
            reify_ = (uu___96_1105.reify_);
            compress_uvars = (uu___96_1105.compress_uvars);
            no_full_norm = (uu___96_1105.no_full_norm);
            check_no_uvars = (uu___96_1105.check_no_uvars);
            unmeta = (uu___96_1105.unmeta);
            unascribe = (uu___96_1105.unascribe)
          }
      | Exclude uu____1106 -> failwith "Bad exclude"
      | Weak  ->
          let uu___97_1107 = fs  in
          {
            beta = (uu___97_1107.beta);
            iota = (uu___97_1107.iota);
            zeta = (uu___97_1107.zeta);
            weak = true;
            hnf = (uu___97_1107.hnf);
            primops = (uu___97_1107.primops);
            eager_unfolding = (uu___97_1107.eager_unfolding);
            inlining = (uu___97_1107.inlining);
            no_delta_steps = (uu___97_1107.no_delta_steps);
            unfold_until = (uu___97_1107.unfold_until);
            unfold_only = (uu___97_1107.unfold_only);
            unfold_attr = (uu___97_1107.unfold_attr);
            unfold_tac = (uu___97_1107.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1107.pure_subterms_within_computations);
            simplify = (uu___97_1107.simplify);
            erase_universes = (uu___97_1107.erase_universes);
            allow_unbound_universes = (uu___97_1107.allow_unbound_universes);
            reify_ = (uu___97_1107.reify_);
            compress_uvars = (uu___97_1107.compress_uvars);
            no_full_norm = (uu___97_1107.no_full_norm);
            check_no_uvars = (uu___97_1107.check_no_uvars);
            unmeta = (uu___97_1107.unmeta);
            unascribe = (uu___97_1107.unascribe)
          }
      | HNF  ->
          let uu___98_1108 = fs  in
          {
            beta = (uu___98_1108.beta);
            iota = (uu___98_1108.iota);
            zeta = (uu___98_1108.zeta);
            weak = (uu___98_1108.weak);
            hnf = true;
            primops = (uu___98_1108.primops);
            eager_unfolding = (uu___98_1108.eager_unfolding);
            inlining = (uu___98_1108.inlining);
            no_delta_steps = (uu___98_1108.no_delta_steps);
            unfold_until = (uu___98_1108.unfold_until);
            unfold_only = (uu___98_1108.unfold_only);
            unfold_attr = (uu___98_1108.unfold_attr);
            unfold_tac = (uu___98_1108.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1108.pure_subterms_within_computations);
            simplify = (uu___98_1108.simplify);
            erase_universes = (uu___98_1108.erase_universes);
            allow_unbound_universes = (uu___98_1108.allow_unbound_universes);
            reify_ = (uu___98_1108.reify_);
            compress_uvars = (uu___98_1108.compress_uvars);
            no_full_norm = (uu___98_1108.no_full_norm);
            check_no_uvars = (uu___98_1108.check_no_uvars);
            unmeta = (uu___98_1108.unmeta);
            unascribe = (uu___98_1108.unascribe)
          }
      | Primops  ->
          let uu___99_1109 = fs  in
          {
            beta = (uu___99_1109.beta);
            iota = (uu___99_1109.iota);
            zeta = (uu___99_1109.zeta);
            weak = (uu___99_1109.weak);
            hnf = (uu___99_1109.hnf);
            primops = true;
            eager_unfolding = (uu___99_1109.eager_unfolding);
            inlining = (uu___99_1109.inlining);
            no_delta_steps = (uu___99_1109.no_delta_steps);
            unfold_until = (uu___99_1109.unfold_until);
            unfold_only = (uu___99_1109.unfold_only);
            unfold_attr = (uu___99_1109.unfold_attr);
            unfold_tac = (uu___99_1109.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1109.pure_subterms_within_computations);
            simplify = (uu___99_1109.simplify);
            erase_universes = (uu___99_1109.erase_universes);
            allow_unbound_universes = (uu___99_1109.allow_unbound_universes);
            reify_ = (uu___99_1109.reify_);
            compress_uvars = (uu___99_1109.compress_uvars);
            no_full_norm = (uu___99_1109.no_full_norm);
            check_no_uvars = (uu___99_1109.check_no_uvars);
            unmeta = (uu___99_1109.unmeta);
            unascribe = (uu___99_1109.unascribe)
          }
      | Eager_unfolding  ->
          let uu___100_1110 = fs  in
          {
            beta = (uu___100_1110.beta);
            iota = (uu___100_1110.iota);
            zeta = (uu___100_1110.zeta);
            weak = (uu___100_1110.weak);
            hnf = (uu___100_1110.hnf);
            primops = (uu___100_1110.primops);
            eager_unfolding = true;
            inlining = (uu___100_1110.inlining);
            no_delta_steps = (uu___100_1110.no_delta_steps);
            unfold_until = (uu___100_1110.unfold_until);
            unfold_only = (uu___100_1110.unfold_only);
            unfold_attr = (uu___100_1110.unfold_attr);
            unfold_tac = (uu___100_1110.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1110.pure_subterms_within_computations);
            simplify = (uu___100_1110.simplify);
            erase_universes = (uu___100_1110.erase_universes);
            allow_unbound_universes = (uu___100_1110.allow_unbound_universes);
            reify_ = (uu___100_1110.reify_);
            compress_uvars = (uu___100_1110.compress_uvars);
            no_full_norm = (uu___100_1110.no_full_norm);
            check_no_uvars = (uu___100_1110.check_no_uvars);
            unmeta = (uu___100_1110.unmeta);
            unascribe = (uu___100_1110.unascribe)
          }
      | Inlining  ->
          let uu___101_1111 = fs  in
          {
            beta = (uu___101_1111.beta);
            iota = (uu___101_1111.iota);
            zeta = (uu___101_1111.zeta);
            weak = (uu___101_1111.weak);
            hnf = (uu___101_1111.hnf);
            primops = (uu___101_1111.primops);
            eager_unfolding = (uu___101_1111.eager_unfolding);
            inlining = true;
            no_delta_steps = (uu___101_1111.no_delta_steps);
            unfold_until = (uu___101_1111.unfold_until);
            unfold_only = (uu___101_1111.unfold_only);
            unfold_attr = (uu___101_1111.unfold_attr);
            unfold_tac = (uu___101_1111.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1111.pure_subterms_within_computations);
            simplify = (uu___101_1111.simplify);
            erase_universes = (uu___101_1111.erase_universes);
            allow_unbound_universes = (uu___101_1111.allow_unbound_universes);
            reify_ = (uu___101_1111.reify_);
            compress_uvars = (uu___101_1111.compress_uvars);
            no_full_norm = (uu___101_1111.no_full_norm);
            check_no_uvars = (uu___101_1111.check_no_uvars);
            unmeta = (uu___101_1111.unmeta);
            unascribe = (uu___101_1111.unascribe)
          }
      | NoDeltaSteps  ->
          let uu___102_1112 = fs  in
          {
            beta = (uu___102_1112.beta);
            iota = (uu___102_1112.iota);
            zeta = (uu___102_1112.zeta);
            weak = (uu___102_1112.weak);
            hnf = (uu___102_1112.hnf);
            primops = (uu___102_1112.primops);
            eager_unfolding = (uu___102_1112.eager_unfolding);
            inlining = (uu___102_1112.inlining);
            no_delta_steps = true;
            unfold_until = (uu___102_1112.unfold_until);
            unfold_only = (uu___102_1112.unfold_only);
            unfold_attr = (uu___102_1112.unfold_attr);
            unfold_tac = (uu___102_1112.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1112.pure_subterms_within_computations);
            simplify = (uu___102_1112.simplify);
            erase_universes = (uu___102_1112.erase_universes);
            allow_unbound_universes = (uu___102_1112.allow_unbound_universes);
            reify_ = (uu___102_1112.reify_);
            compress_uvars = (uu___102_1112.compress_uvars);
            no_full_norm = (uu___102_1112.no_full_norm);
            check_no_uvars = (uu___102_1112.check_no_uvars);
            unmeta = (uu___102_1112.unmeta);
            unascribe = (uu___102_1112.unascribe)
          }
      | UnfoldUntil d ->
          let uu___103_1114 = fs  in
          {
            beta = (uu___103_1114.beta);
            iota = (uu___103_1114.iota);
            zeta = (uu___103_1114.zeta);
            weak = (uu___103_1114.weak);
            hnf = (uu___103_1114.hnf);
            primops = (uu___103_1114.primops);
            eager_unfolding = (uu___103_1114.eager_unfolding);
            inlining = (uu___103_1114.inlining);
            no_delta_steps = (uu___103_1114.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___103_1114.unfold_only);
            unfold_attr = (uu___103_1114.unfold_attr);
            unfold_tac = (uu___103_1114.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1114.pure_subterms_within_computations);
            simplify = (uu___103_1114.simplify);
            erase_universes = (uu___103_1114.erase_universes);
            allow_unbound_universes = (uu___103_1114.allow_unbound_universes);
            reify_ = (uu___103_1114.reify_);
            compress_uvars = (uu___103_1114.compress_uvars);
            no_full_norm = (uu___103_1114.no_full_norm);
            check_no_uvars = (uu___103_1114.check_no_uvars);
            unmeta = (uu___103_1114.unmeta);
            unascribe = (uu___103_1114.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___104_1118 = fs  in
          {
            beta = (uu___104_1118.beta);
            iota = (uu___104_1118.iota);
            zeta = (uu___104_1118.zeta);
            weak = (uu___104_1118.weak);
            hnf = (uu___104_1118.hnf);
            primops = (uu___104_1118.primops);
            eager_unfolding = (uu___104_1118.eager_unfolding);
            inlining = (uu___104_1118.inlining);
            no_delta_steps = (uu___104_1118.no_delta_steps);
            unfold_until = (uu___104_1118.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___104_1118.unfold_attr);
            unfold_tac = (uu___104_1118.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1118.pure_subterms_within_computations);
            simplify = (uu___104_1118.simplify);
            erase_universes = (uu___104_1118.erase_universes);
            allow_unbound_universes = (uu___104_1118.allow_unbound_universes);
            reify_ = (uu___104_1118.reify_);
            compress_uvars = (uu___104_1118.compress_uvars);
            no_full_norm = (uu___104_1118.no_full_norm);
            check_no_uvars = (uu___104_1118.check_no_uvars);
            unmeta = (uu___104_1118.unmeta);
            unascribe = (uu___104_1118.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___105_1122 = fs  in
          {
            beta = (uu___105_1122.beta);
            iota = (uu___105_1122.iota);
            zeta = (uu___105_1122.zeta);
            weak = (uu___105_1122.weak);
            hnf = (uu___105_1122.hnf);
            primops = (uu___105_1122.primops);
            eager_unfolding = (uu___105_1122.eager_unfolding);
            inlining = (uu___105_1122.inlining);
            no_delta_steps = (uu___105_1122.no_delta_steps);
            unfold_until = (uu___105_1122.unfold_until);
            unfold_only = (uu___105_1122.unfold_only);
            unfold_attr = (FStar_Pervasives_Native.Some attr);
            unfold_tac = (uu___105_1122.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1122.pure_subterms_within_computations);
            simplify = (uu___105_1122.simplify);
            erase_universes = (uu___105_1122.erase_universes);
            allow_unbound_universes = (uu___105_1122.allow_unbound_universes);
            reify_ = (uu___105_1122.reify_);
            compress_uvars = (uu___105_1122.compress_uvars);
            no_full_norm = (uu___105_1122.no_full_norm);
            check_no_uvars = (uu___105_1122.check_no_uvars);
            unmeta = (uu___105_1122.unmeta);
            unascribe = (uu___105_1122.unascribe)
          }
      | UnfoldTac  ->
          let uu___106_1123 = fs  in
          {
            beta = (uu___106_1123.beta);
            iota = (uu___106_1123.iota);
            zeta = (uu___106_1123.zeta);
            weak = (uu___106_1123.weak);
            hnf = (uu___106_1123.hnf);
            primops = (uu___106_1123.primops);
            eager_unfolding = (uu___106_1123.eager_unfolding);
            inlining = (uu___106_1123.inlining);
            no_delta_steps = (uu___106_1123.no_delta_steps);
            unfold_until = (uu___106_1123.unfold_until);
            unfold_only = (uu___106_1123.unfold_only);
            unfold_attr = (uu___106_1123.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___106_1123.pure_subterms_within_computations);
            simplify = (uu___106_1123.simplify);
            erase_universes = (uu___106_1123.erase_universes);
            allow_unbound_universes = (uu___106_1123.allow_unbound_universes);
            reify_ = (uu___106_1123.reify_);
            compress_uvars = (uu___106_1123.compress_uvars);
            no_full_norm = (uu___106_1123.no_full_norm);
            check_no_uvars = (uu___106_1123.check_no_uvars);
            unmeta = (uu___106_1123.unmeta);
            unascribe = (uu___106_1123.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___107_1124 = fs  in
          {
            beta = (uu___107_1124.beta);
            iota = (uu___107_1124.iota);
            zeta = (uu___107_1124.zeta);
            weak = (uu___107_1124.weak);
            hnf = (uu___107_1124.hnf);
            primops = (uu___107_1124.primops);
            eager_unfolding = (uu___107_1124.eager_unfolding);
            inlining = (uu___107_1124.inlining);
            no_delta_steps = (uu___107_1124.no_delta_steps);
            unfold_until = (uu___107_1124.unfold_until);
            unfold_only = (uu___107_1124.unfold_only);
            unfold_attr = (uu___107_1124.unfold_attr);
            unfold_tac = (uu___107_1124.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___107_1124.simplify);
            erase_universes = (uu___107_1124.erase_universes);
            allow_unbound_universes = (uu___107_1124.allow_unbound_universes);
            reify_ = (uu___107_1124.reify_);
            compress_uvars = (uu___107_1124.compress_uvars);
            no_full_norm = (uu___107_1124.no_full_norm);
            check_no_uvars = (uu___107_1124.check_no_uvars);
            unmeta = (uu___107_1124.unmeta);
            unascribe = (uu___107_1124.unascribe)
          }
      | Simplify  ->
          let uu___108_1125 = fs  in
          {
            beta = (uu___108_1125.beta);
            iota = (uu___108_1125.iota);
            zeta = (uu___108_1125.zeta);
            weak = (uu___108_1125.weak);
            hnf = (uu___108_1125.hnf);
            primops = (uu___108_1125.primops);
            eager_unfolding = (uu___108_1125.eager_unfolding);
            inlining = (uu___108_1125.inlining);
            no_delta_steps = (uu___108_1125.no_delta_steps);
            unfold_until = (uu___108_1125.unfold_until);
            unfold_only = (uu___108_1125.unfold_only);
            unfold_attr = (uu___108_1125.unfold_attr);
            unfold_tac = (uu___108_1125.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1125.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___108_1125.erase_universes);
            allow_unbound_universes = (uu___108_1125.allow_unbound_universes);
            reify_ = (uu___108_1125.reify_);
            compress_uvars = (uu___108_1125.compress_uvars);
            no_full_norm = (uu___108_1125.no_full_norm);
            check_no_uvars = (uu___108_1125.check_no_uvars);
            unmeta = (uu___108_1125.unmeta);
            unascribe = (uu___108_1125.unascribe)
          }
      | EraseUniverses  ->
          let uu___109_1126 = fs  in
          {
            beta = (uu___109_1126.beta);
            iota = (uu___109_1126.iota);
            zeta = (uu___109_1126.zeta);
            weak = (uu___109_1126.weak);
            hnf = (uu___109_1126.hnf);
            primops = (uu___109_1126.primops);
            eager_unfolding = (uu___109_1126.eager_unfolding);
            inlining = (uu___109_1126.inlining);
            no_delta_steps = (uu___109_1126.no_delta_steps);
            unfold_until = (uu___109_1126.unfold_until);
            unfold_only = (uu___109_1126.unfold_only);
            unfold_attr = (uu___109_1126.unfold_attr);
            unfold_tac = (uu___109_1126.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1126.pure_subterms_within_computations);
            simplify = (uu___109_1126.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___109_1126.allow_unbound_universes);
            reify_ = (uu___109_1126.reify_);
            compress_uvars = (uu___109_1126.compress_uvars);
            no_full_norm = (uu___109_1126.no_full_norm);
            check_no_uvars = (uu___109_1126.check_no_uvars);
            unmeta = (uu___109_1126.unmeta);
            unascribe = (uu___109_1126.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___110_1127 = fs  in
          {
            beta = (uu___110_1127.beta);
            iota = (uu___110_1127.iota);
            zeta = (uu___110_1127.zeta);
            weak = (uu___110_1127.weak);
            hnf = (uu___110_1127.hnf);
            primops = (uu___110_1127.primops);
            eager_unfolding = (uu___110_1127.eager_unfolding);
            inlining = (uu___110_1127.inlining);
            no_delta_steps = (uu___110_1127.no_delta_steps);
            unfold_until = (uu___110_1127.unfold_until);
            unfold_only = (uu___110_1127.unfold_only);
            unfold_attr = (uu___110_1127.unfold_attr);
            unfold_tac = (uu___110_1127.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1127.pure_subterms_within_computations);
            simplify = (uu___110_1127.simplify);
            erase_universes = (uu___110_1127.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___110_1127.reify_);
            compress_uvars = (uu___110_1127.compress_uvars);
            no_full_norm = (uu___110_1127.no_full_norm);
            check_no_uvars = (uu___110_1127.check_no_uvars);
            unmeta = (uu___110_1127.unmeta);
            unascribe = (uu___110_1127.unascribe)
          }
      | Reify  ->
          let uu___111_1128 = fs  in
          {
            beta = (uu___111_1128.beta);
            iota = (uu___111_1128.iota);
            zeta = (uu___111_1128.zeta);
            weak = (uu___111_1128.weak);
            hnf = (uu___111_1128.hnf);
            primops = (uu___111_1128.primops);
            eager_unfolding = (uu___111_1128.eager_unfolding);
            inlining = (uu___111_1128.inlining);
            no_delta_steps = (uu___111_1128.no_delta_steps);
            unfold_until = (uu___111_1128.unfold_until);
            unfold_only = (uu___111_1128.unfold_only);
            unfold_attr = (uu___111_1128.unfold_attr);
            unfold_tac = (uu___111_1128.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1128.pure_subterms_within_computations);
            simplify = (uu___111_1128.simplify);
            erase_universes = (uu___111_1128.erase_universes);
            allow_unbound_universes = (uu___111_1128.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___111_1128.compress_uvars);
            no_full_norm = (uu___111_1128.no_full_norm);
            check_no_uvars = (uu___111_1128.check_no_uvars);
            unmeta = (uu___111_1128.unmeta);
            unascribe = (uu___111_1128.unascribe)
          }
      | CompressUvars  ->
          let uu___112_1129 = fs  in
          {
            beta = (uu___112_1129.beta);
            iota = (uu___112_1129.iota);
            zeta = (uu___112_1129.zeta);
            weak = (uu___112_1129.weak);
            hnf = (uu___112_1129.hnf);
            primops = (uu___112_1129.primops);
            eager_unfolding = (uu___112_1129.eager_unfolding);
            inlining = (uu___112_1129.inlining);
            no_delta_steps = (uu___112_1129.no_delta_steps);
            unfold_until = (uu___112_1129.unfold_until);
            unfold_only = (uu___112_1129.unfold_only);
            unfold_attr = (uu___112_1129.unfold_attr);
            unfold_tac = (uu___112_1129.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1129.pure_subterms_within_computations);
            simplify = (uu___112_1129.simplify);
            erase_universes = (uu___112_1129.erase_universes);
            allow_unbound_universes = (uu___112_1129.allow_unbound_universes);
            reify_ = (uu___112_1129.reify_);
            compress_uvars = true;
            no_full_norm = (uu___112_1129.no_full_norm);
            check_no_uvars = (uu___112_1129.check_no_uvars);
            unmeta = (uu___112_1129.unmeta);
            unascribe = (uu___112_1129.unascribe)
          }
      | NoFullNorm  ->
          let uu___113_1130 = fs  in
          {
            beta = (uu___113_1130.beta);
            iota = (uu___113_1130.iota);
            zeta = (uu___113_1130.zeta);
            weak = (uu___113_1130.weak);
            hnf = (uu___113_1130.hnf);
            primops = (uu___113_1130.primops);
            eager_unfolding = (uu___113_1130.eager_unfolding);
            inlining = (uu___113_1130.inlining);
            no_delta_steps = (uu___113_1130.no_delta_steps);
            unfold_until = (uu___113_1130.unfold_until);
            unfold_only = (uu___113_1130.unfold_only);
            unfold_attr = (uu___113_1130.unfold_attr);
            unfold_tac = (uu___113_1130.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1130.pure_subterms_within_computations);
            simplify = (uu___113_1130.simplify);
            erase_universes = (uu___113_1130.erase_universes);
            allow_unbound_universes = (uu___113_1130.allow_unbound_universes);
            reify_ = (uu___113_1130.reify_);
            compress_uvars = (uu___113_1130.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___113_1130.check_no_uvars);
            unmeta = (uu___113_1130.unmeta);
            unascribe = (uu___113_1130.unascribe)
          }
      | CheckNoUvars  ->
          let uu___114_1131 = fs  in
          {
            beta = (uu___114_1131.beta);
            iota = (uu___114_1131.iota);
            zeta = (uu___114_1131.zeta);
            weak = (uu___114_1131.weak);
            hnf = (uu___114_1131.hnf);
            primops = (uu___114_1131.primops);
            eager_unfolding = (uu___114_1131.eager_unfolding);
            inlining = (uu___114_1131.inlining);
            no_delta_steps = (uu___114_1131.no_delta_steps);
            unfold_until = (uu___114_1131.unfold_until);
            unfold_only = (uu___114_1131.unfold_only);
            unfold_attr = (uu___114_1131.unfold_attr);
            unfold_tac = (uu___114_1131.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1131.pure_subterms_within_computations);
            simplify = (uu___114_1131.simplify);
            erase_universes = (uu___114_1131.erase_universes);
            allow_unbound_universes = (uu___114_1131.allow_unbound_universes);
            reify_ = (uu___114_1131.reify_);
            compress_uvars = (uu___114_1131.compress_uvars);
            no_full_norm = (uu___114_1131.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___114_1131.unmeta);
            unascribe = (uu___114_1131.unascribe)
          }
      | Unmeta  ->
          let uu___115_1132 = fs  in
          {
            beta = (uu___115_1132.beta);
            iota = (uu___115_1132.iota);
            zeta = (uu___115_1132.zeta);
            weak = (uu___115_1132.weak);
            hnf = (uu___115_1132.hnf);
            primops = (uu___115_1132.primops);
            eager_unfolding = (uu___115_1132.eager_unfolding);
            inlining = (uu___115_1132.inlining);
            no_delta_steps = (uu___115_1132.no_delta_steps);
            unfold_until = (uu___115_1132.unfold_until);
            unfold_only = (uu___115_1132.unfold_only);
            unfold_attr = (uu___115_1132.unfold_attr);
            unfold_tac = (uu___115_1132.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1132.pure_subterms_within_computations);
            simplify = (uu___115_1132.simplify);
            erase_universes = (uu___115_1132.erase_universes);
            allow_unbound_universes = (uu___115_1132.allow_unbound_universes);
            reify_ = (uu___115_1132.reify_);
            compress_uvars = (uu___115_1132.compress_uvars);
            no_full_norm = (uu___115_1132.no_full_norm);
            check_no_uvars = (uu___115_1132.check_no_uvars);
            unmeta = true;
            unascribe = (uu___115_1132.unascribe)
          }
      | Unascribe  ->
          let uu___116_1133 = fs  in
          {
            beta = (uu___116_1133.beta);
            iota = (uu___116_1133.iota);
            zeta = (uu___116_1133.zeta);
            weak = (uu___116_1133.weak);
            hnf = (uu___116_1133.hnf);
            primops = (uu___116_1133.primops);
            eager_unfolding = (uu___116_1133.eager_unfolding);
            inlining = (uu___116_1133.inlining);
            no_delta_steps = (uu___116_1133.no_delta_steps);
            unfold_until = (uu___116_1133.unfold_until);
            unfold_only = (uu___116_1133.unfold_only);
            unfold_attr = (uu___116_1133.unfold_attr);
            unfold_tac = (uu___116_1133.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1133.pure_subterms_within_computations);
            simplify = (uu___116_1133.simplify);
            erase_universes = (uu___116_1133.erase_universes);
            allow_unbound_universes = (uu___116_1133.allow_unbound_universes);
            reify_ = (uu___116_1133.reify_);
            compress_uvars = (uu___116_1133.compress_uvars);
            no_full_norm = (uu___116_1133.no_full_norm);
            check_no_uvars = (uu___116_1133.check_no_uvars);
            unmeta = (uu___116_1133.unmeta);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1165  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1366 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1468 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1479 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___74_1498  ->
    match uu___74_1498 with
    | Clos (uu____1499,t,uu____1501,uu____1502) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1547 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____1913 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____1949 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____1985 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2054 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2096 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2152 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2192 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2224 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2260 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2276 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____2301 .
    'Auu____2301 ->
      FStar_Range.range -> 'Auu____2301 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2355 = FStar_ST.op_Bang r  in
          match uu____2355 with
          | FStar_Pervasives_Native.Some uu____2403 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2457 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2457 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___75_2464  ->
    match uu___75_2464 with
    | Arg (c,uu____2466,uu____2467) ->
        let uu____2468 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2468
    | MemoLazy uu____2469 -> "MemoLazy"
    | Abs (uu____2476,bs,uu____2478,uu____2479,uu____2480) ->
        let uu____2485 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2485
    | UnivArgs uu____2490 -> "UnivArgs"
    | Match uu____2497 -> "Match"
    | App (uu____2504,t,uu____2506,uu____2507) ->
        let uu____2508 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2508
    | Meta (m,uu____2510) -> "Meta"
    | Let uu____2511 -> "Let"
    | Cfg uu____2520 -> "Cfg"
    | Debug (t,uu____2522) ->
        let uu____2523 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2523
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2531 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2531 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2562 . 'Auu____2562 Prims.list -> Prims.bool =
  fun uu___76_2568  ->
    match uu___76_2568 with | [] -> true | uu____2571 -> false
  
let lookup_bvar :
  'Auu____2578 'Auu____2579 .
    ('Auu____2579,'Auu____2578) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2578
  =
  fun env  ->
    fun x  ->
      try
        let uu____2603 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2603
      with
      | uu____2616 ->
          let uu____2617 =
            let uu____2618 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2618  in
          failwith uu____2617
  
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
          let uu____2655 =
            FStar_List.fold_left
              (fun uu____2681  ->
                 fun u1  ->
                   match uu____2681 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2706 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2706 with
                        | (k_u,n1) ->
                            let uu____2721 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2721
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2655 with
          | (uu____2739,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2764 =
                   let uu____2765 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2765  in
                 match uu____2764 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2783 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2791 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2797 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2806 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2815 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2822 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2822 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2839 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2839 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2847 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2855 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2855 with
                                  | (uu____2860,m) -> n1 <= m))
                           in
                        if uu____2847 then rest1 else us1
                    | uu____2865 -> us1)
               | uu____2870 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2874 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2874
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2878 = aux u  in
           match uu____2878 with
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
          (fun uu____2982  ->
             let uu____2983 = FStar_Syntax_Print.tag_of_term t  in
             let uu____2984 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2983
               uu____2984);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____2991 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2993 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3018 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3019 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3020 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3021 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3038 =
                      let uu____3039 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3040 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3039 uu____3040
                       in
                    failwith uu____3038
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3043 =
                    let uu____3044 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3044  in
                  mk uu____3043 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3051 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3051
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3053 = lookup_bvar env x  in
                  (match uu____3053 with
                   | Univ uu____3056 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3059,uu____3060) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3172 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3172 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3200 =
                         let uu____3201 =
                           let uu____3218 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3218)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3201  in
                       mk uu____3200 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3249 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3249 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3291 =
                    let uu____3302 =
                      let uu____3309 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3309]  in
                    closures_as_binders_delayed cfg env uu____3302  in
                  (match uu____3291 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3327 =
                         let uu____3328 =
                           let uu____3335 =
                             let uu____3336 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3336
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3335, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3328  in
                       mk uu____3327 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3427 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3427
                    | FStar_Util.Inr c ->
                        let uu____3441 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3441
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3457 =
                    let uu____3458 =
                      let uu____3485 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3485, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3458  in
                  mk uu____3457 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3536 =
                    let uu____3537 =
                      let uu____3544 = closure_as_term_delayed cfg env t'  in
                      let uu____3547 =
                        let uu____3548 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3548  in
                      (uu____3544, uu____3547)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3537  in
                  mk uu____3536 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3608 =
                    let uu____3609 =
                      let uu____3616 = closure_as_term_delayed cfg env t'  in
                      let uu____3619 =
                        let uu____3620 =
                          let uu____3627 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3627)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3620  in
                      (uu____3616, uu____3619)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3609  in
                  mk uu____3608 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3646 =
                    let uu____3647 =
                      let uu____3654 = closure_as_term_delayed cfg env t'  in
                      let uu____3657 =
                        let uu____3658 =
                          let uu____3667 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3667)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3658  in
                      (uu____3654, uu____3657)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3647  in
                  mk uu____3646 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3680 =
                    let uu____3681 =
                      let uu____3688 = closure_as_term_delayed cfg env t'  in
                      (uu____3688, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3681  in
                  mk uu____3680 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3728  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3747 =
                    let uu____3758 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3758
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3777 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___121_3789 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_3789.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_3789.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3777))
                     in
                  (match uu____3747 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___122_3805 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___122_3805.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___122_3805.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3816,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3875  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3900 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3900
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3920  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____3942 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3942
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___123_3954 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___123_3954.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___123_3954.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___124_3955 = lb  in
                    let uu____3956 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___124_3955.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___124_3955.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3956
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3986  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4075 =
                    match uu____4075 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4130 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4151 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4211  ->
                                        fun uu____4212  ->
                                          match (uu____4211, uu____4212) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4303 =
                                                norm_pat env3 p1  in
                                              (match uu____4303 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4151 with
                               | (pats1,env3) ->
                                   ((let uu___125_4385 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___125_4385.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___126_4404 = x  in
                                let uu____4405 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___126_4404.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___126_4404.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4405
                                }  in
                              ((let uu___127_4419 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___127_4419.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___128_4430 = x  in
                                let uu____4431 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___128_4430.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___128_4430.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4431
                                }  in
                              ((let uu___129_4445 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___129_4445.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___130_4461 = x  in
                                let uu____4462 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_4461.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_4461.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4462
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___131_4469 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___131_4469.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4472 = norm_pat env1 pat  in
                        (match uu____4472 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4501 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4501
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4507 =
                    let uu____4508 =
                      let uu____4531 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4531)  in
                    FStar_Syntax_Syntax.Tm_match uu____4508  in
                  mk uu____4507 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4617 -> closure_as_term cfg env t

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
        | uu____4643 ->
            FStar_List.map
              (fun uu____4660  ->
                 match uu____4660 with
                 | (x,imp) ->
                     let uu____4679 = closure_as_term_delayed cfg env x  in
                     (uu____4679, imp)) args

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
        let uu____4693 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4742  ->
                  fun uu____4743  ->
                    match (uu____4742, uu____4743) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___132_4813 = b  in
                          let uu____4814 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___132_4813.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___132_4813.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4814
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4693 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4907 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4920 = closure_as_term_delayed cfg env t  in
                 let uu____4921 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4920 uu____4921
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4934 = closure_as_term_delayed cfg env t  in
                 let uu____4935 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4934 uu____4935
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
                        (fun uu___77_4961  ->
                           match uu___77_4961 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4965 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____4965
                           | f -> f))
                    in
                 let uu____4969 =
                   let uu___133_4970 = c1  in
                   let uu____4971 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4971;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___133_4970.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4969)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___78_4981  ->
            match uu___78_4981 with
            | FStar_Syntax_Syntax.DECREASES uu____4982 -> false
            | uu____4985 -> true))

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
                   (fun uu___79_5003  ->
                      match uu___79_5003 with
                      | FStar_Syntax_Syntax.DECREASES uu____5004 -> false
                      | uu____5007 -> true))
               in
            let rc1 =
              let uu___134_5009 = rc  in
              let uu____5010 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___134_5009.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5010;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5017 -> lopt

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
    let uu____5102 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5102  in
  let arg_as_bounded_int uu____5130 =
    match uu____5130 with
    | (a,uu____5142) ->
        let uu____5149 =
          let uu____5150 = FStar_Syntax_Subst.compress a  in
          uu____5150.FStar_Syntax_Syntax.n  in
        (match uu____5149 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5160;
                FStar_Syntax_Syntax.vars = uu____5161;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5163;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5164;_},uu____5165)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5204 =
               let uu____5209 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5209)  in
             FStar_Pervasives_Native.Some uu____5204
         | uu____5214 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5254 = f a  in FStar_Pervasives_Native.Some uu____5254
    | uu____5255 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5303 = f a0 a1  in FStar_Pervasives_Native.Some uu____5303
    | uu____5304 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5346 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5346)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5395 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5395)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5419 =
    match uu____5419 with
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
                   let uu____5467 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5467)) a429 a430)
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
                       let uu____5495 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5495)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5516 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5516)) a436
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
                       let uu____5544 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5544)) a439
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
                       let uu____5572 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5572))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5680 =
          let uu____5689 = as_a a  in
          let uu____5692 = as_b b  in (uu____5689, uu____5692)  in
        (match uu____5680 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5707 =
               let uu____5708 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5708  in
             FStar_Pervasives_Native.Some uu____5707
         | uu____5709 -> FStar_Pervasives_Native.None)
    | uu____5718 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5732 =
        let uu____5733 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5733  in
      mk uu____5732 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5743 =
      let uu____5746 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5746  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5743  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5778 =
      let uu____5779 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5779  in
    FStar_Syntax_Embeddings.embed_int rng uu____5778  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5797 = arg_as_string a1  in
        (match uu____5797 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5803 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5803 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5816 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5816
              | uu____5817 -> FStar_Pervasives_Native.None)
         | uu____5822 -> FStar_Pervasives_Native.None)
    | uu____5825 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5835 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5835  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5859 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5870 =
          let uu____5891 = arg_as_string fn  in
          let uu____5894 = arg_as_int from_line  in
          let uu____5897 = arg_as_int from_col  in
          let uu____5900 = arg_as_int to_line  in
          let uu____5903 = arg_as_int to_col  in
          (uu____5891, uu____5894, uu____5897, uu____5900, uu____5903)  in
        (match uu____5870 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5934 =
                 let uu____5935 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5936 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5935 uu____5936  in
               let uu____5937 =
                 let uu____5938 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5939 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5938 uu____5939  in
               FStar_Range.mk_range fn1 uu____5934 uu____5937  in
             let uu____5940 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____5940
         | uu____5945 -> FStar_Pervasives_Native.None)
    | uu____5966 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5993)::(a1,uu____5995)::(a2,uu____5997)::[] ->
        let uu____6034 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6034 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6047 -> FStar_Pervasives_Native.None)
    | uu____6048 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6075)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6084 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6108 =
      let uu____6123 =
        let uu____6138 =
          let uu____6153 =
            let uu____6168 =
              let uu____6183 =
                let uu____6198 =
                  let uu____6213 =
                    let uu____6228 =
                      let uu____6243 =
                        let uu____6258 =
                          let uu____6273 =
                            let uu____6288 =
                              let uu____6303 =
                                let uu____6318 =
                                  let uu____6333 =
                                    let uu____6348 =
                                      let uu____6363 =
                                        let uu____6378 =
                                          let uu____6393 =
                                            let uu____6408 =
                                              let uu____6423 =
                                                let uu____6436 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6436,
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
                                              let uu____6443 =
                                                let uu____6458 =
                                                  let uu____6471 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6471,
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
                                                let uu____6478 =
                                                  let uu____6493 =
                                                    let uu____6508 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6508,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6517 =
                                                    let uu____6534 =
                                                      let uu____6549 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6549,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6558 =
                                                      let uu____6575 =
                                                        let uu____6594 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6594,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6575]  in
                                                    uu____6534 :: uu____6558
                                                     in
                                                  uu____6493 :: uu____6517
                                                   in
                                                uu____6458 :: uu____6478  in
                                              uu____6423 :: uu____6443  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6408
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6393
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
                                          :: uu____6378
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
                                        :: uu____6363
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
                                      :: uu____6348
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
                                                        let uu____6811 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6811 y)) a466
                                                a467 a468)))
                                    :: uu____6333
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6318
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6303
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6288
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6273
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6258
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6243
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
                                          let uu____6978 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____6978)) a470 a471 a472)))
                      :: uu____6228
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
                                        let uu____7004 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7004)) a474 a475 a476)))
                    :: uu____6213
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
                                      let uu____7030 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7030)) a478 a479 a480)))
                  :: uu____6198
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
                                    let uu____7056 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7056)) a482 a483 a484)))
                :: uu____6183
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6168
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6153
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6138
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6123
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6108
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7209 =
        let uu____7210 =
          let uu____7211 = FStar_Syntax_Syntax.as_arg c  in [uu____7211]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7210  in
      uu____7209 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7261 =
                let uu____7274 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7274, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7290  ->
                                    fun uu____7291  ->
                                      match (uu____7290, uu____7291) with
                                      | ((int_to_t1,x),(uu____7310,y)) ->
                                          let uu____7320 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7320)) a486 a487 a488)))
                 in
              let uu____7321 =
                let uu____7336 =
                  let uu____7349 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7349, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7365  ->
                                      fun uu____7366  ->
                                        match (uu____7365, uu____7366) with
                                        | ((int_to_t1,x),(uu____7385,y)) ->
                                            let uu____7395 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7395)) a490 a491 a492)))
                   in
                let uu____7396 =
                  let uu____7411 =
                    let uu____7424 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7424, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7440  ->
                                        fun uu____7441  ->
                                          match (uu____7440, uu____7441) with
                                          | ((int_to_t1,x),(uu____7460,y)) ->
                                              let uu____7470 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7470)) a494 a495 a496)))
                     in
                  let uu____7471 =
                    let uu____7486 =
                      let uu____7499 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7499, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7511  ->
                                        match uu____7511 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7486]  in
                  uu____7411 :: uu____7471  in
                uu____7336 :: uu____7396  in
              uu____7261 :: uu____7321))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7625 =
                let uu____7638 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7638, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7654  ->
                                    fun uu____7655  ->
                                      match (uu____7654, uu____7655) with
                                      | ((int_to_t1,x),(uu____7674,y)) ->
                                          let uu____7684 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7684)) a501 a502 a503)))
                 in
              let uu____7685 =
                let uu____7700 =
                  let uu____7713 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7713, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7729  ->
                                      fun uu____7730  ->
                                        match (uu____7729, uu____7730) with
                                        | ((int_to_t1,x),(uu____7749,y)) ->
                                            let uu____7759 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7759)) a505 a506 a507)))
                   in
                [uu____7700]  in
              uu____7625 :: uu____7685))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let (equality_ops : primitive_step Prims.list) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7849)::(a1,uu____7851)::(a2,uu____7853)::[] ->
        let uu____7890 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7890 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___135_7896 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___135_7896.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___135_7896.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___136_7900 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_7900.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_7900.FStar_Syntax_Syntax.vars)
                })
         | uu____7901 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7903)::uu____7904::(a1,uu____7906)::(a2,uu____7908)::[] ->
        let uu____7957 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7957 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___135_7963 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___135_7963.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___135_7963.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___136_7967 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_7967.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_7967.FStar_Syntax_Syntax.vars)
                })
         | uu____7968 -> FStar_Pervasives_Native.None)
    | uu____7969 -> failwith "Unexpected number of arguments"  in
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
      let uu____7988 =
        let uu____7989 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____7989 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____7988
    with | uu____7995 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____7999 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7999) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8059  ->
           fun subst1  ->
             match uu____8059 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8100,uu____8101)) ->
                      let uu____8160 = b  in
                      (match uu____8160 with
                       | (bv,uu____8168) ->
                           let uu____8169 =
                             let uu____8170 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____8170  in
                           if uu____8169
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8175 = unembed_binder term1  in
                              match uu____8175 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8182 =
                                      let uu___139_8183 = bv  in
                                      let uu____8184 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___139_8183.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___139_8183.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8184
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8182
                                     in
                                  let b_for_x =
                                    let uu____8188 =
                                      let uu____8195 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8195)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8188  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___80_8204  ->
                                         match uu___80_8204 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8205,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8207;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8208;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8213 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8214 -> subst1)) env []
  
let reduce_primops :
  'Auu____8231 'Auu____8232 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8232) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8231 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____8273 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).primops  in
          if uu____8273
          then tm
          else
            (let uu____8275 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8275 with
             | (head1,args) ->
                 let uu____8312 =
                   let uu____8313 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8313.FStar_Syntax_Syntax.n  in
                 (match uu____8312 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8317 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps
                         in
                      (match uu____8317 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8334  ->
                                   let uu____8335 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8336 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8343 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8335 uu____8336 uu____8343);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8348  ->
                                   let uu____8349 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8349);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8352  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8354 =
                                 prim_step.interpretation psc args  in
                               match uu____8354 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8360  ->
                                         let uu____8361 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8361);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8367  ->
                                         let uu____8368 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8369 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8368 uu____8369);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8370 ->
                           (log_primops cfg
                              (fun uu____8374  ->
                                 let uu____8375 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8375);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8379  ->
                            let uu____8380 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8380);
                       (match args with
                        | (a1,uu____8382)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8399 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8411  ->
                            let uu____8412 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8412);
                       (match args with
                        | (t,uu____8414)::(r,uu____8416)::[] ->
                            let uu____8443 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8443 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___140_8447 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___140_8447.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___140_8447.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8450 -> tm))
                  | uu____8459 -> tm))
  
let reduce_equality :
  'Auu____8464 'Auu____8465 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8465) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8464 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___141_8503 = cfg  in
         {
           steps =
             (let uu___142_8506 = default_steps  in
              {
                beta = (uu___142_8506.beta);
                iota = (uu___142_8506.iota);
                zeta = (uu___142_8506.zeta);
                weak = (uu___142_8506.weak);
                hnf = (uu___142_8506.hnf);
                primops = true;
                eager_unfolding = (uu___142_8506.eager_unfolding);
                inlining = (uu___142_8506.inlining);
                no_delta_steps = (uu___142_8506.no_delta_steps);
                unfold_until = (uu___142_8506.unfold_until);
                unfold_only = (uu___142_8506.unfold_only);
                unfold_attr = (uu___142_8506.unfold_attr);
                unfold_tac = (uu___142_8506.unfold_tac);
                pure_subterms_within_computations =
                  (uu___142_8506.pure_subterms_within_computations);
                simplify = (uu___142_8506.simplify);
                erase_universes = (uu___142_8506.erase_universes);
                allow_unbound_universes =
                  (uu___142_8506.allow_unbound_universes);
                reify_ = (uu___142_8506.reify_);
                compress_uvars = (uu___142_8506.compress_uvars);
                no_full_norm = (uu___142_8506.no_full_norm);
                check_no_uvars = (uu___142_8506.check_no_uvars);
                unmeta = (uu___142_8506.unmeta);
                unascribe = (uu___142_8506.unascribe)
              });
           tcenv = (uu___141_8503.tcenv);
           debug = (uu___141_8503.debug);
           delta_level = (uu___141_8503.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___141_8503.strong);
           memoize_lazy = (uu___141_8503.memoize_lazy);
           normalize_pure_lets = (uu___141_8503.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8513 'Auu____8514 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8514) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8513 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8556 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8556
          then tm1
          else
            (let w t =
               let uu___143_8568 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___143_8568.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___143_8568.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8584;
                      FStar_Syntax_Syntax.vars = uu____8585;_},uu____8586)
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
                      FStar_Syntax_Syntax.pos = uu____8593;
                      FStar_Syntax_Syntax.vars = uu____8594;_},uu____8595)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8601 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8606 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8606
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8627 =
                 match uu____8627 with
                 | (t1,q) ->
                     let uu____8640 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8640 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8668 -> (t1, q))
                  in
               let uu____8677 = FStar_Syntax_Util.head_and_args t  in
               match uu____8677 with
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
                         FStar_Syntax_Syntax.pos = uu____8774;
                         FStar_Syntax_Syntax.vars = uu____8775;_},uu____8776);
                    FStar_Syntax_Syntax.pos = uu____8777;
                    FStar_Syntax_Syntax.vars = uu____8778;_},args)
                 ->
                 let uu____8804 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8804
                 then
                   let uu____8805 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8805 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8860)::
                        (uu____8861,(arg,uu____8863))::[] ->
                        maybe_auto_squash arg
                    | (uu____8928,(arg,uu____8930))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8931)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8996)::uu____8997::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9060::(FStar_Pervasives_Native.Some (false
                                   ),uu____9061)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9124 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9140 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9140
                    then
                      let uu____9141 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9141 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9196)::uu____9197::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9260::(FStar_Pervasives_Native.Some (true
                                     ),uu____9261)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9324)::
                          (uu____9325,(arg,uu____9327))::[] ->
                          maybe_auto_squash arg
                      | (uu____9392,(arg,uu____9394))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9395)::[]
                          -> maybe_auto_squash arg
                      | uu____9460 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9476 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9476
                       then
                         let uu____9477 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9477 with
                         | uu____9532::(FStar_Pervasives_Native.Some (true
                                        ),uu____9533)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9596)::uu____9597::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9660)::
                             (uu____9661,(arg,uu____9663))::[] ->
                             maybe_auto_squash arg
                         | (uu____9728,(p,uu____9730))::(uu____9731,(q,uu____9733))::[]
                             ->
                             let uu____9798 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9798
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9800 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9816 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9816
                          then
                            let uu____9817 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9817 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9872)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9911)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9950 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____9966 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____9966
                             then
                               match args with
                               | (t,uu____9968)::[] ->
                                   let uu____9985 =
                                     let uu____9986 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____9986.FStar_Syntax_Syntax.n  in
                                   (match uu____9985 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9989::[],body,uu____9991) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10018 -> tm1)
                                    | uu____10021 -> tm1)
                               | (uu____10022,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10023))::
                                   (t,uu____10025)::[] ->
                                   let uu____10064 =
                                     let uu____10065 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10065.FStar_Syntax_Syntax.n  in
                                   (match uu____10064 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10068::[],body,uu____10070) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10097 -> tm1)
                                    | uu____10100 -> tm1)
                               | uu____10101 -> tm1
                             else
                               (let uu____10111 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10111
                                then
                                  match args with
                                  | (t,uu____10113)::[] ->
                                      let uu____10130 =
                                        let uu____10131 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10131.FStar_Syntax_Syntax.n  in
                                      (match uu____10130 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10134::[],body,uu____10136)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10163 -> tm1)
                                       | uu____10166 -> tm1)
                                  | (uu____10167,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10168))::(t,uu____10170)::[] ->
                                      let uu____10209 =
                                        let uu____10210 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10210.FStar_Syntax_Syntax.n  in
                                      (match uu____10209 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10213::[],body,uu____10215)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10242 -> tm1)
                                       | uu____10245 -> tm1)
                                  | uu____10246 -> tm1
                                else
                                  (let uu____10256 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10256
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10257;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10258;_},uu____10259)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10276;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10277;_},uu____10278)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10295 -> tm1
                                   else
                                     (let uu____10305 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10305 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10325 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10335;
                    FStar_Syntax_Syntax.vars = uu____10336;_},args)
                 ->
                 let uu____10358 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____10358
                 then
                   let uu____10359 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____10359 with
                    | (FStar_Pervasives_Native.Some (true ),uu____10414)::
                        (uu____10415,(arg,uu____10417))::[] ->
                        maybe_auto_squash arg
                    | (uu____10482,(arg,uu____10484))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____10485)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____10550)::uu____10551::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10614::(FStar_Pervasives_Native.Some (false
                                    ),uu____10615)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10678 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____10694 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____10694
                    then
                      let uu____10695 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____10695 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10750)::uu____10751::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10814::(FStar_Pervasives_Native.Some (true
                                      ),uu____10815)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____10878)::
                          (uu____10879,(arg,uu____10881))::[] ->
                          maybe_auto_squash arg
                      | (uu____10946,(arg,uu____10948))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10949)::[]
                          -> maybe_auto_squash arg
                      | uu____11014 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11030 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11030
                       then
                         let uu____11031 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11031 with
                         | uu____11086::(FStar_Pervasives_Native.Some (true
                                         ),uu____11087)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11150)::uu____11151::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11214)::
                             (uu____11215,(arg,uu____11217))::[] ->
                             maybe_auto_squash arg
                         | (uu____11282,(p,uu____11284))::(uu____11285,
                                                           (q,uu____11287))::[]
                             ->
                             let uu____11352 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____11352
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11354 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____11370 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____11370
                          then
                            let uu____11371 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____11371 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____11426)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____11465)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____11504 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____11520 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____11520
                             then
                               match args with
                               | (t,uu____11522)::[] ->
                                   let uu____11539 =
                                     let uu____11540 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11540.FStar_Syntax_Syntax.n  in
                                   (match uu____11539 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11543::[],body,uu____11545) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11572 -> tm1)
                                    | uu____11575 -> tm1)
                               | (uu____11576,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____11577))::
                                   (t,uu____11579)::[] ->
                                   let uu____11618 =
                                     let uu____11619 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11619.FStar_Syntax_Syntax.n  in
                                   (match uu____11618 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11622::[],body,uu____11624) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11651 -> tm1)
                                    | uu____11654 -> tm1)
                               | uu____11655 -> tm1
                             else
                               (let uu____11665 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____11665
                                then
                                  match args with
                                  | (t,uu____11667)::[] ->
                                      let uu____11684 =
                                        let uu____11685 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11685.FStar_Syntax_Syntax.n  in
                                      (match uu____11684 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11688::[],body,uu____11690)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11717 -> tm1)
                                       | uu____11720 -> tm1)
                                  | (uu____11721,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____11722))::(t,uu____11724)::[] ->
                                      let uu____11763 =
                                        let uu____11764 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11764.FStar_Syntax_Syntax.n  in
                                      (match uu____11763 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11767::[],body,uu____11769)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11796 -> tm1)
                                       | uu____11799 -> tm1)
                                  | uu____11800 -> tm1
                                else
                                  (let uu____11810 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____11810
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11811;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11812;_},uu____11813)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11830;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11831;_},uu____11832)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11849 -> tm1
                                   else
                                     (let uu____11859 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____11859 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____11879 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____11894 -> tm1)
  
let maybe_simplify :
  'Auu____11901 'Auu____11902 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11902) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11901 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____11945 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11946 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____11945
               uu____11946)
          else ();
          tm'
  
let is_norm_request :
  'Auu____11952 .
    FStar_Syntax_Syntax.term -> 'Auu____11952 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11965 =
        let uu____11972 =
          let uu____11973 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11973.FStar_Syntax_Syntax.n  in
        (uu____11972, args)  in
      match uu____11965 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11979::uu____11980::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11984::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11989::uu____11990::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11993 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___81_12004  ->
    match uu___81_12004 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12010 =
          let uu____12013 =
            let uu____12014 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____12014  in
          [uu____12013]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____12010
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12030 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____12030) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____12068 =
          let uu____12071 =
            let uu____12076 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____12076 s  in
          FStar_All.pipe_right uu____12071 FStar_Util.must  in
        FStar_All.pipe_right uu____12068 tr_norm_steps  in
      match args with
      | uu____12101::(tm,uu____12103)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____12126)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____12141)::uu____12142::(tm,uu____12144)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____12184 =
              let uu____12187 = full_norm steps  in parse_steps uu____12187
               in
            Beta :: uu____12184  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____12196 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___82_12213  ->
    match uu___82_12213 with
    | (App
        (uu____12216,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12217;
                       FStar_Syntax_Syntax.vars = uu____12218;_},uu____12219,uu____12220))::uu____12221
        -> true
    | uu____12228 -> false
  
let firstn :
  'Auu____12234 .
    Prims.int ->
      'Auu____12234 Prims.list ->
        ('Auu____12234 Prims.list,'Auu____12234 Prims.list)
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
          (uu____12270,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12271;
                         FStar_Syntax_Syntax.vars = uu____12272;_},uu____12273,uu____12274))::uu____12275
          -> (cfg.steps).reify_
      | uu____12282 -> false
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let r =
        let uu____12292 = FStar_Syntax_Util.eq_tm a a'  in
        match uu____12292 with
        | FStar_Syntax_Util.Equal  -> true
        | uu____12293 -> false  in
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12435 ->
                   let uu____12460 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12460
               | uu____12461 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12469  ->
               let uu____12470 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12471 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12472 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12479 =
                 let uu____12480 =
                   let uu____12483 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12483
                    in
                 stack_to_string uu____12480  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12470 uu____12471 uu____12472 uu____12479);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12506 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12507 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12508;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12509;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12512;
                 FStar_Syntax_Syntax.fv_delta = uu____12513;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12514;
                 FStar_Syntax_Syntax.fv_delta = uu____12515;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12516);_}
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
                 let uu___144_12558 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___144_12558.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___144_12558.FStar_Syntax_Syntax.vars)
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
                 let uu___145_12596 = cfg  in
                 {
                   steps =
                     (let uu___146_12599 = cfg.steps  in
                      {
                        beta = (uu___146_12599.beta);
                        iota = (uu___146_12599.iota);
                        zeta = (uu___146_12599.zeta);
                        weak = (uu___146_12599.weak);
                        hnf = (uu___146_12599.hnf);
                        primops = (uu___146_12599.primops);
                        eager_unfolding = (uu___146_12599.eager_unfolding);
                        inlining = (uu___146_12599.inlining);
                        no_delta_steps = false;
                        unfold_until = (uu___146_12599.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___146_12599.unfold_attr);
                        unfold_tac = (uu___146_12599.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___146_12599.pure_subterms_within_computations);
                        simplify = (uu___146_12599.simplify);
                        erase_universes = (uu___146_12599.erase_universes);
                        allow_unbound_universes =
                          (uu___146_12599.allow_unbound_universes);
                        reify_ = (uu___146_12599.reify_);
                        compress_uvars = (uu___146_12599.compress_uvars);
                        no_full_norm = (uu___146_12599.no_full_norm);
                        check_no_uvars = (uu___146_12599.check_no_uvars);
                        unmeta = (uu___146_12599.unmeta);
                        unascribe = (uu___146_12599.unascribe)
                      });
                   tcenv = (uu___145_12596.tcenv);
                   debug = (uu___145_12596.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___145_12596.primitive_steps);
                   strong = (uu___145_12596.strong);
                   memoize_lazy = (uu___145_12596.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12602 = get_norm_request (norm cfg' env []) args  in
               (match uu____12602 with
                | (s,tm) ->
                    let delta_level =
                      let uu____12618 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___83_12623  ->
                                match uu___83_12623 with
                                | UnfoldUntil uu____12624 -> true
                                | UnfoldOnly uu____12625 -> true
                                | uu____12628 -> false))
                         in
                      if uu____12618
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___147_12633 = cfg  in
                      let uu____12634 = to_fsteps s  in
                      {
                        steps = uu____12634;
                        tcenv = (uu___147_12633.tcenv);
                        debug = (uu___147_12633.debug);
                        delta_level;
                        primitive_steps = (uu___147_12633.primitive_steps);
                        strong = (uu___147_12633.strong);
                        memoize_lazy = (uu___147_12633.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12643 =
                          let uu____12644 =
                            let uu____12649 = FStar_Util.now ()  in
                            (t1, uu____12649)  in
                          Debug uu____12644  in
                        uu____12643 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12653 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12653
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12662 =
                      let uu____12669 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12669, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12662  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12679 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12679  in
               let uu____12680 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12680
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12686  ->
                       let uu____12687 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12688 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12687 uu____12688);
                  if b
                  then
                    (let uu____12689 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12689 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___84_12698  ->
                            match uu___84_12698 with
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
                    should_delta &&
                      (match (cfg.steps).unfold_only with
                       | FStar_Pervasives_Native.None  -> true
                       | FStar_Pervasives_Native.Some lids ->
                           FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                     in
                  let should_delta2 =
                    if Prims.op_Negation should_delta1
                    then false
                    else
                      (let tac_opaque_attr =
                         FStar_Syntax_Util.exp_string "tac_opaque"  in
                       let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       (match (attrs, ((cfg.steps).unfold_attr)) with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Pervasives_Native.Some at) -> false
                        | (FStar_Pervasives_Native.Some
                           ats,FStar_Pervasives_Native.Some at) ->
                            FStar_Util.for_some (attr_eq at) ats
                        | (uu____12745,uu____12746) -> true) &&
                         (if (cfg.steps).unfold_tac
                          then
                            let uu____12760 =
                              cases
                                (FStar_Util.for_some
                                   (attr_eq tac_opaque_attr)) false attrs
                               in
                            FStar_All.pipe_left Prims.op_Negation uu____12760
                          else true))
                     in
                  log cfg
                    (fun uu____12769  ->
                       let uu____12770 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12771 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____12772 =
                         FStar_Util.string_of_bool should_delta2  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____12770
                         uu____12771 uu____12772);
                  if should_delta2
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12775 = lookup_bvar env x  in
               (match uu____12775 with
                | Univ uu____12778 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12827 = FStar_ST.op_Bang r  in
                      (match uu____12827 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12945  ->
                                 let uu____12946 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12947 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12946
                                   uu____12947);
                            (let uu____12948 =
                               let uu____12949 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____12949.FStar_Syntax_Syntax.n  in
                             match uu____12948 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12952 ->
                                 norm cfg env2 stack t'
                             | uu____12969 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13039)::uu____13040 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____13049)::uu____13050 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____13060,uu____13061))::stack_rest ->
                    (match c with
                     | Univ uu____13065 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13074 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13095  ->
                                    let uu____13096 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13096);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13136  ->
                                    let uu____13137 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13137);
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
                       (fun uu____13215  ->
                          let uu____13216 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13216);
                     norm cfg env stack1 t1)
                | (Debug uu____13217)::uu____13218 ->
                    if (cfg.steps).weak
                    then
                      let uu____13225 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13225
                    else
                      (let uu____13227 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13227 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13269  -> dummy :: env1) env)
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
                                          let uu____13306 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13306)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_13311 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_13311.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_13311.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13312 -> lopt  in
                           (log cfg
                              (fun uu____13318  ->
                                 let uu____13319 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13319);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_13328 = cfg  in
                               {
                                 steps = (uu___149_13328.steps);
                                 tcenv = (uu___149_13328.tcenv);
                                 debug = (uu___149_13328.debug);
                                 delta_level = (uu___149_13328.delta_level);
                                 primitive_steps =
                                   (uu___149_13328.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_13328.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_13328.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13339)::uu____13340 ->
                    if (cfg.steps).weak
                    then
                      let uu____13347 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13347
                    else
                      (let uu____13349 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13349 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13391  -> dummy :: env1) env)
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
                                          let uu____13428 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13428)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_13433 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_13433.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_13433.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13434 -> lopt  in
                           (log cfg
                              (fun uu____13440  ->
                                 let uu____13441 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13441);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_13450 = cfg  in
                               {
                                 steps = (uu___149_13450.steps);
                                 tcenv = (uu___149_13450.tcenv);
                                 debug = (uu___149_13450.debug);
                                 delta_level = (uu___149_13450.delta_level);
                                 primitive_steps =
                                   (uu___149_13450.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_13450.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_13450.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13461)::uu____13462 ->
                    if (cfg.steps).weak
                    then
                      let uu____13473 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13473
                    else
                      (let uu____13475 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13475 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13517  -> dummy :: env1) env)
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
                                          let uu____13554 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13554)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_13559 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_13559.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_13559.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13560 -> lopt  in
                           (log cfg
                              (fun uu____13566  ->
                                 let uu____13567 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13567);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_13576 = cfg  in
                               {
                                 steps = (uu___149_13576.steps);
                                 tcenv = (uu___149_13576.tcenv);
                                 debug = (uu___149_13576.debug);
                                 delta_level = (uu___149_13576.delta_level);
                                 primitive_steps =
                                   (uu___149_13576.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_13576.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_13576.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13587)::uu____13588 ->
                    if (cfg.steps).weak
                    then
                      let uu____13599 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13599
                    else
                      (let uu____13601 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13601 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13643  -> dummy :: env1) env)
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
                                          let uu____13680 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13680)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_13685 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_13685.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_13685.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13686 -> lopt  in
                           (log cfg
                              (fun uu____13692  ->
                                 let uu____13693 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13693);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_13702 = cfg  in
                               {
                                 steps = (uu___149_13702.steps);
                                 tcenv = (uu___149_13702.tcenv);
                                 debug = (uu___149_13702.debug);
                                 delta_level = (uu___149_13702.delta_level);
                                 primitive_steps =
                                   (uu___149_13702.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_13702.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_13702.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13713)::uu____13714 ->
                    if (cfg.steps).weak
                    then
                      let uu____13729 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13729
                    else
                      (let uu____13731 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13731 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13773  -> dummy :: env1) env)
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
                                          let uu____13810 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13810)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_13815 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_13815.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_13815.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13816 -> lopt  in
                           (log cfg
                              (fun uu____13822  ->
                                 let uu____13823 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13823);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_13832 = cfg  in
                               {
                                 steps = (uu___149_13832.steps);
                                 tcenv = (uu___149_13832.tcenv);
                                 debug = (uu___149_13832.debug);
                                 delta_level = (uu___149_13832.delta_level);
                                 primitive_steps =
                                   (uu___149_13832.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_13832.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_13832.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____13843 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13843
                    else
                      (let uu____13845 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13845 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13887  -> dummy :: env1) env)
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
                                          let uu____13924 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13924)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_13929 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_13929.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_13929.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13930 -> lopt  in
                           (log cfg
                              (fun uu____13936  ->
                                 let uu____13937 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13937);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_13946 = cfg  in
                               {
                                 steps = (uu___149_13946.steps);
                                 tcenv = (uu___149_13946.tcenv);
                                 debug = (uu___149_13946.debug);
                                 delta_level = (uu___149_13946.delta_level);
                                 primitive_steps =
                                   (uu___149_13946.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_13946.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_13946.normalize_pure_lets)
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
                      (fun uu____13995  ->
                         fun stack1  ->
                           match uu____13995 with
                           | (a,aq) ->
                               let uu____14007 =
                                 let uu____14008 =
                                   let uu____14015 =
                                     let uu____14016 =
                                       let uu____14047 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____14047, false)  in
                                     Clos uu____14016  in
                                   (uu____14015, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____14008  in
                               uu____14007 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14131  ->
                     let uu____14132 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14132);
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
                             ((let uu___150_14168 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___150_14168.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___150_14168.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14169 ->
                      let uu____14174 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14174)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14177 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14177 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14208 =
                          let uu____14209 =
                            let uu____14216 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___151_14218 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___151_14218.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___151_14218.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14216)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14209  in
                        mk uu____14208 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14237 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14237
               else
                 (let uu____14239 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14239 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14247 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14271  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14247 c1  in
                      let t2 =
                        let uu____14293 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14293 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14404)::uu____14405 ->
                    (log cfg
                       (fun uu____14416  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14417)::uu____14418 ->
                    (log cfg
                       (fun uu____14429  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14430,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14431;
                                   FStar_Syntax_Syntax.vars = uu____14432;_},uu____14433,uu____14434))::uu____14435
                    ->
                    (log cfg
                       (fun uu____14444  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14445)::uu____14446 ->
                    (log cfg
                       (fun uu____14457  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14458 ->
                    (log cfg
                       (fun uu____14461  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14465  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14482 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14482
                         | FStar_Util.Inr c ->
                             let uu____14490 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14490
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14503 =
                               let uu____14504 =
                                 let uu____14531 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14531, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14504
                                in
                             mk uu____14503 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14550 ->
                           let uu____14551 =
                             let uu____14552 =
                               let uu____14553 =
                                 let uu____14580 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14580, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14553
                                in
                             mk uu____14552 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14551))))
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
                         let uu____14690 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14690 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___152_14710 = cfg  in
                               let uu____14711 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___152_14710.steps);
                                 tcenv = uu____14711;
                                 debug = (uu___152_14710.debug);
                                 delta_level = (uu___152_14710.delta_level);
                                 primitive_steps =
                                   (uu___152_14710.primitive_steps);
                                 strong = (uu___152_14710.strong);
                                 memoize_lazy = (uu___152_14710.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_14710.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14716 =
                                 let uu____14717 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14717  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14716
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___153_14720 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___153_14720.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___153_14720.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             }))
                  in
               let uu____14721 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14721
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14732,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14733;
                               FStar_Syntax_Syntax.lbunivs = uu____14734;
                               FStar_Syntax_Syntax.lbtyp = uu____14735;
                               FStar_Syntax_Syntax.lbeff = uu____14736;
                               FStar_Syntax_Syntax.lbdef = uu____14737;_}::uu____14738),uu____14739)
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
                   let uu____14776 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14776  in
                 let env1 =
                   let uu____14786 =
                     let uu____14793 =
                       let uu____14794 =
                         let uu____14825 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14825,
                           false)
                          in
                       Clos uu____14794  in
                     ((FStar_Pervasives_Native.Some binder), uu____14793)  in
                   uu____14786 :: env  in
                 (log cfg
                    (fun uu____14918  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14922  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14923 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14923))
                 else
                   (let uu____14925 =
                      let uu____14930 =
                        let uu____14931 =
                          let uu____14932 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14932
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14931]  in
                      FStar_Syntax_Subst.open_term uu____14930 body  in
                    match uu____14925 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14941  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14949 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14949  in
                            FStar_Util.Inl
                              (let uu___154_14959 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___154_14959.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___154_14959.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14962  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___155_14964 = lb  in
                             let uu____14965 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___155_14964.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_14964.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14965
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15000  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___156_15023 = cfg  in
                             {
                               steps = (uu___156_15023.steps);
                               tcenv = (uu___156_15023.tcenv);
                               debug = (uu___156_15023.debug);
                               delta_level = (uu___156_15023.delta_level);
                               primitive_steps =
                                 (uu___156_15023.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___156_15023.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_15023.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15026  ->
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
               let uu____15043 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15043 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15079 =
                               let uu___157_15080 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_15080.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_15080.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15079  in
                           let uu____15081 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15081 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15107 =
                                   FStar_List.map (fun uu____15123  -> dummy)
                                     lbs1
                                    in
                                 let uu____15124 =
                                   let uu____15133 =
                                     FStar_List.map
                                       (fun uu____15153  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15133 env  in
                                 FStar_List.append uu____15107 uu____15124
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15177 =
                                       let uu___158_15178 = rc  in
                                       let uu____15179 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___158_15178.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15179;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___158_15178.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15177
                                 | uu____15186 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___159_15190 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___159_15190.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___159_15190.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
                      let uu____15200 =
                        FStar_List.map (fun uu____15216  -> dummy) lbs2  in
                      FStar_List.append uu____15200 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15224 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15224 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___160_15240 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___160_15240.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___160_15240.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15267 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15267
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15286 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15362  ->
                        match uu____15362 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___161_15483 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___161_15483.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___161_15483.FStar_Syntax_Syntax.sort)
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
               (match uu____15286 with
                | (rec_env,memos,uu____15696) ->
                    let uu____15749 =
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
                             let uu____16060 =
                               let uu____16067 =
                                 let uu____16068 =
                                   let uu____16099 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16099, false)
                                    in
                                 Clos uu____16068  in
                               (FStar_Pervasives_Native.None, uu____16067)
                                in
                             uu____16060 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16209  ->
                     let uu____16210 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16210);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16232 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16234::uu____16235 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16240) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16241 ->
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
                             | uu____16272 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16286 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16286
                              | uu____16297 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16301 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16327 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16345 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16362 =
                        let uu____16363 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16364 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16363 uu____16364
                         in
                      failwith uu____16362
                    else rebuild cfg env stack t2
                | uu____16366 -> norm cfg env stack t2))

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
                let uu____16376 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16376  in
              let uu____16377 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16377 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16390  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16401  ->
                        let uu____16402 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16403 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16402 uu____16403);
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
                      | (UnivArgs (us',uu____16416))::stack1 ->
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
                      | uu____16471 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____16474 ->
                          let uu____16477 =
                            let uu____16478 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16478
                             in
                          failwith uu____16477
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
                  let uu___162_16499 = cfg  in
                  let uu____16500 =
                    to_fsteps
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps]
                     in
                  {
                    steps = uu____16500;
                    tcenv = (uu___162_16499.tcenv);
                    debug = (uu___162_16499.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___162_16499.primitive_steps);
                    strong = (uu___162_16499.strong);
                    memoize_lazy = (uu___162_16499.memoize_lazy);
                    normalize_pure_lets =
                      (uu___162_16499.normalize_pure_lets)
                  }
                else
                  (let uu___163_16502 = cfg  in
                   {
                     steps =
                       (let uu___164_16505 = cfg.steps  in
                        {
                          beta = (uu___164_16505.beta);
                          iota = (uu___164_16505.iota);
                          zeta = false;
                          weak = (uu___164_16505.weak);
                          hnf = (uu___164_16505.hnf);
                          primops = (uu___164_16505.primops);
                          eager_unfolding = (uu___164_16505.eager_unfolding);
                          inlining = (uu___164_16505.inlining);
                          no_delta_steps = (uu___164_16505.no_delta_steps);
                          unfold_until = (uu___164_16505.unfold_until);
                          unfold_only = (uu___164_16505.unfold_only);
                          unfold_attr = (uu___164_16505.unfold_attr);
                          unfold_tac = (uu___164_16505.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___164_16505.pure_subterms_within_computations);
                          simplify = (uu___164_16505.simplify);
                          erase_universes = (uu___164_16505.erase_universes);
                          allow_unbound_universes =
                            (uu___164_16505.allow_unbound_universes);
                          reify_ = (uu___164_16505.reify_);
                          compress_uvars = (uu___164_16505.compress_uvars);
                          no_full_norm = (uu___164_16505.no_full_norm);
                          check_no_uvars = (uu___164_16505.check_no_uvars);
                          unmeta = (uu___164_16505.unmeta);
                          unascribe = (uu___164_16505.unascribe)
                        });
                     tcenv = (uu___163_16502.tcenv);
                     debug = (uu___163_16502.debug);
                     delta_level = (uu___163_16502.delta_level);
                     primitive_steps = (uu___163_16502.primitive_steps);
                     strong = (uu___163_16502.strong);
                     memoize_lazy = (uu___163_16502.memoize_lazy);
                     normalize_pure_lets =
                       (uu___163_16502.normalize_pure_lets)
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
                  (fun uu____16535  ->
                     let uu____16536 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16537 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16536
                       uu____16537);
                (let uu____16538 =
                   let uu____16539 = FStar_Syntax_Subst.compress head2  in
                   uu____16539.FStar_Syntax_Syntax.n  in
                 match uu____16538 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16557 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16557 with
                      | (uu____16558,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16564 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16572 =
                                   let uu____16573 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16573.FStar_Syntax_Syntax.n  in
                                 match uu____16572 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16579,uu____16580))
                                     ->
                                     let uu____16589 =
                                       let uu____16590 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16590.FStar_Syntax_Syntax.n  in
                                     (match uu____16589 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16596,msrc,uu____16598))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16607 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16607
                                      | uu____16608 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16609 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16610 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16610 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___165_16615 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___165_16615.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___165_16615.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___165_16615.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      }  in
                                    let uu____16616 = FStar_List.tl stack  in
                                    let uu____16617 =
                                      let uu____16618 =
                                        let uu____16621 =
                                          let uu____16622 =
                                            let uu____16635 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16635)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16622
                                           in
                                        FStar_Syntax_Syntax.mk uu____16621
                                         in
                                      uu____16618
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16616 uu____16617
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16651 =
                                      let uu____16652 = is_return body  in
                                      match uu____16652 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16656;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16657;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16662 -> false  in
                                    if uu____16651
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
                                         let uu____16685 =
                                           let uu____16688 =
                                             let uu____16689 =
                                               let uu____16706 =
                                                 let uu____16709 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16709]  in
                                               (uu____16706, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16689
                                              in
                                           FStar_Syntax_Syntax.mk uu____16688
                                            in
                                         uu____16685
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16725 =
                                           let uu____16726 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16726.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16725 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16732::uu____16733::[])
                                             ->
                                             let uu____16740 =
                                               let uu____16743 =
                                                 let uu____16744 =
                                                   let uu____16751 =
                                                     let uu____16754 =
                                                       let uu____16755 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16755
                                                        in
                                                     let uu____16756 =
                                                       let uu____16759 =
                                                         let uu____16760 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16760
                                                          in
                                                       [uu____16759]  in
                                                     uu____16754 ::
                                                       uu____16756
                                                      in
                                                   (bind1, uu____16751)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16744
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16743
                                                in
                                             uu____16740
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16768 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____16774 =
                                           let uu____16777 =
                                             let uu____16778 =
                                               let uu____16793 =
                                                 let uu____16796 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16797 =
                                                   let uu____16800 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____16801 =
                                                     let uu____16804 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16805 =
                                                       let uu____16808 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____16809 =
                                                         let uu____16812 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16813 =
                                                           let uu____16816 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16816]  in
                                                         uu____16812 ::
                                                           uu____16813
                                                          in
                                                       uu____16808 ::
                                                         uu____16809
                                                        in
                                                     uu____16804 ::
                                                       uu____16805
                                                      in
                                                   uu____16800 :: uu____16801
                                                    in
                                                 uu____16796 :: uu____16797
                                                  in
                                               (bind_inst, uu____16793)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16778
                                              in
                                           FStar_Syntax_Syntax.mk uu____16777
                                            in
                                         uu____16774
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16828  ->
                                            let uu____16829 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16830 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16829 uu____16830);
                                       (let uu____16831 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16831 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16855 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16855 with
                      | (uu____16856,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16891 =
                                  let uu____16892 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16892.FStar_Syntax_Syntax.n  in
                                match uu____16891 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16898) -> t2
                                | uu____16903 -> head3  in
                              let uu____16904 =
                                let uu____16905 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16905.FStar_Syntax_Syntax.n  in
                              match uu____16904 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16911 -> FStar_Pervasives_Native.None
                               in
                            let uu____16912 = maybe_extract_fv head3  in
                            match uu____16912 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16922 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16922
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____16927 = maybe_extract_fv head4
                                     in
                                  match uu____16927 with
                                  | FStar_Pervasives_Native.Some uu____16932
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16933 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____16938 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16953 =
                              match uu____16953 with
                              | (e,q) ->
                                  let uu____16960 =
                                    let uu____16961 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16961.FStar_Syntax_Syntax.n  in
                                  (match uu____16960 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____16976 -> false)
                               in
                            let uu____16977 =
                              let uu____16978 =
                                let uu____16985 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16985 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16978
                               in
                            if uu____16977
                            then
                              let uu____16990 =
                                let uu____16991 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16991
                                 in
                              failwith uu____16990
                            else ());
                           (let uu____16993 = maybe_unfold_action head_app
                               in
                            match uu____16993 with
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
                                   (fun uu____17034  ->
                                      let uu____17035 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17036 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17035 uu____17036);
                                 (let uu____17037 = FStar_List.tl stack  in
                                  norm cfg env uu____17037 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17039) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17063 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17063  in
                     (log cfg
                        (fun uu____17067  ->
                           let uu____17068 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17068);
                      (let uu____17069 = FStar_List.tl stack  in
                       norm cfg env uu____17069 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____17071) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17196  ->
                               match uu____17196 with
                               | (pat,wopt,tm) ->
                                   let uu____17244 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17244)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____17276 = FStar_List.tl stack  in
                     norm cfg env uu____17276 tm
                 | uu____17277 -> fallback ())

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
              (fun uu____17291  ->
                 let uu____17292 = FStar_Ident.string_of_lid msrc  in
                 let uu____17293 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17294 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17292
                   uu____17293 uu____17294);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____17296 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17296 with
               | (uu____17297,return_repr) ->
                   let return_inst =
                     let uu____17306 =
                       let uu____17307 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17307.FStar_Syntax_Syntax.n  in
                     match uu____17306 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17313::[]) ->
                         let uu____17320 =
                           let uu____17323 =
                             let uu____17324 =
                               let uu____17331 =
                                 let uu____17334 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17334]  in
                               (return_tm, uu____17331)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17324  in
                           FStar_Syntax_Syntax.mk uu____17323  in
                         uu____17320 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17342 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17345 =
                     let uu____17348 =
                       let uu____17349 =
                         let uu____17364 =
                           let uu____17367 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17368 =
                             let uu____17371 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17371]  in
                           uu____17367 :: uu____17368  in
                         (return_inst, uu____17364)  in
                       FStar_Syntax_Syntax.Tm_app uu____17349  in
                     FStar_Syntax_Syntax.mk uu____17348  in
                   uu____17345 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17380 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17380 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17383 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17383
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17384;
                     FStar_TypeChecker_Env.mtarget = uu____17385;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17386;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17401 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17401
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17402;
                     FStar_TypeChecker_Env.mtarget = uu____17403;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17404;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17428 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17429 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17428 t FStar_Syntax_Syntax.tun uu____17429)

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
                (fun uu____17485  ->
                   match uu____17485 with
                   | (a,imp) ->
                       let uu____17496 = norm cfg env [] a  in
                       (uu____17496, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___166_17510 = comp  in
            let uu____17511 =
              let uu____17512 =
                let uu____17521 = norm cfg env [] t  in
                let uu____17522 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17521, uu____17522)  in
              FStar_Syntax_Syntax.Total uu____17512  in
            {
              FStar_Syntax_Syntax.n = uu____17511;
              FStar_Syntax_Syntax.pos =
                (uu___166_17510.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_17510.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___167_17537 = comp  in
            let uu____17538 =
              let uu____17539 =
                let uu____17548 = norm cfg env [] t  in
                let uu____17549 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17548, uu____17549)  in
              FStar_Syntax_Syntax.GTotal uu____17539  in
            {
              FStar_Syntax_Syntax.n = uu____17538;
              FStar_Syntax_Syntax.pos =
                (uu___167_17537.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_17537.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____17601  ->
                      match uu____17601 with
                      | (a,i) ->
                          let uu____17612 = norm cfg env [] a  in
                          (uu____17612, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_17623  ->
                      match uu___85_17623 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17627 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____17627
                      | f -> f))
               in
            let uu___168_17631 = comp  in
            let uu____17632 =
              let uu____17633 =
                let uu___169_17634 = ct  in
                let uu____17635 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____17636 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____17639 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____17635;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___169_17634.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____17636;
                  FStar_Syntax_Syntax.effect_args = uu____17639;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____17633  in
            {
              FStar_Syntax_Syntax.n = uu____17632;
              FStar_Syntax_Syntax.pos =
                (uu___168_17631.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_17631.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17650  ->
        match uu____17650 with
        | (x,imp) ->
            let uu____17653 =
              let uu___170_17654 = x  in
              let uu____17655 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___170_17654.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___170_17654.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17655
              }  in
            (uu____17653, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17661 =
          FStar_List.fold_left
            (fun uu____17679  ->
               fun b  ->
                 match uu____17679 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17661 with | (nbs,uu____17719) -> FStar_List.rev nbs

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
            let uu____17735 =
              let uu___171_17736 = rc  in
              let uu____17737 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___171_17736.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17737;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___171_17736.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17735
        | uu____17744 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17757  ->
               let uu____17758 = FStar_Syntax_Print.tag_of_term t  in
               let uu____17759 = FStar_Syntax_Print.term_to_string t  in
               let uu____17760 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____17767 =
                 let uu____17768 =
                   let uu____17771 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17771
                    in
                 stack_to_string uu____17768  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____17758 uu____17759 uu____17760 uu____17767);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____17802 =
                     let uu____17803 =
                       let uu____17804 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____17804  in
                     FStar_Util.string_of_int uu____17803  in
                   let uu____17809 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____17810 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17802 uu____17809 uu____17810)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____17864  ->
                     let uu____17865 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17865);
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
               let uu____17901 =
                 let uu___172_17902 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___172_17902.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___172_17902.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____17901
           | (Arg (Univ uu____17903,uu____17904,uu____17905))::uu____17906 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17909,uu____17910))::uu____17911 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____17927),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17980  ->
                     let uu____17981 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17981);
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
                  (let uu____17991 = FStar_ST.op_Bang m  in
                   match uu____17991 with
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
                   | FStar_Pervasives_Native.Some (uu____18128,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____18175 =
                 log cfg
                   (fun uu____18179  ->
                      let uu____18180 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18180);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____18184 =
                 let uu____18185 = FStar_Syntax_Subst.compress t1  in
                 uu____18185.FStar_Syntax_Syntax.n  in
               (match uu____18184 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18212 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____18212  in
                    (log cfg
                       (fun uu____18216  ->
                          let uu____18217 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18217);
                     (let uu____18218 = FStar_List.tl stack  in
                      norm cfg env1 uu____18218 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18219);
                       FStar_Syntax_Syntax.pos = uu____18220;
                       FStar_Syntax_Syntax.vars = uu____18221;_},(e,uu____18223)::[])
                    -> norm cfg env1 stack' e
                | uu____18252 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18272  ->
                     let uu____18273 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18273);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____18278 =
                   log cfg
                     (fun uu____18283  ->
                        let uu____18284 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____18285 =
                          let uu____18286 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18303  ->
                                    match uu____18303 with
                                    | (p,uu____18313,uu____18314) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____18286
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18284 uu____18285);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_18331  ->
                                match uu___86_18331 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18332 -> false))
                         in
                      let uu___173_18333 = cfg  in
                      {
                        steps =
                          (let uu___174_18336 = cfg.steps  in
                           {
                             beta = (uu___174_18336.beta);
                             iota = (uu___174_18336.iota);
                             zeta = false;
                             weak = (uu___174_18336.weak);
                             hnf = (uu___174_18336.hnf);
                             primops = (uu___174_18336.primops);
                             eager_unfolding =
                               (uu___174_18336.eager_unfolding);
                             inlining = (uu___174_18336.inlining);
                             no_delta_steps = (uu___174_18336.no_delta_steps);
                             unfold_until = (uu___174_18336.unfold_until);
                             unfold_only = (uu___174_18336.unfold_only);
                             unfold_attr = (uu___174_18336.unfold_attr);
                             unfold_tac = (uu___174_18336.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___174_18336.pure_subterms_within_computations);
                             simplify = (uu___174_18336.simplify);
                             erase_universes =
                               (uu___174_18336.erase_universes);
                             allow_unbound_universes =
                               (uu___174_18336.allow_unbound_universes);
                             reify_ = (uu___174_18336.reify_);
                             compress_uvars = (uu___174_18336.compress_uvars);
                             no_full_norm = (uu___174_18336.no_full_norm);
                             check_no_uvars = (uu___174_18336.check_no_uvars);
                             unmeta = (uu___174_18336.unmeta);
                             unascribe = (uu___174_18336.unascribe)
                           });
                        tcenv = (uu___173_18333.tcenv);
                        debug = (uu___173_18333.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___173_18333.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___173_18333.memoize_lazy);
                        normalize_pure_lets =
                          (uu___173_18333.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18368 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18389 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18449  ->
                                    fun uu____18450  ->
                                      match (uu____18449, uu____18450) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18541 = norm_pat env3 p1
                                             in
                                          (match uu____18541 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____18389 with
                           | (pats1,env3) ->
                               ((let uu___175_18623 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___175_18623.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___176_18642 = x  in
                            let uu____18643 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___176_18642.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___176_18642.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18643
                            }  in
                          ((let uu___177_18657 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___177_18657.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___178_18668 = x  in
                            let uu____18669 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_18668.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_18668.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18669
                            }  in
                          ((let uu___179_18683 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___179_18683.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___180_18699 = x  in
                            let uu____18700 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___180_18699.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___180_18699.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18700
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___181_18707 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___181_18707.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18717 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18731 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____18731 with
                                  | (p,wopt,e) ->
                                      let uu____18751 = norm_pat env1 p  in
                                      (match uu____18751 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18776 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18776
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____18782 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____18782)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18792) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18797 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18798;
                         FStar_Syntax_Syntax.fv_delta = uu____18799;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18800;
                         FStar_Syntax_Syntax.fv_delta = uu____18801;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18802);_}
                       -> true
                   | uu____18809 -> false  in
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
                   let uu____18954 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____18954 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____19041 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19080 ->
                                 let uu____19081 =
                                   let uu____19082 = is_cons head1  in
                                   Prims.op_Negation uu____19082  in
                                 FStar_Util.Inr uu____19081)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19107 =
                              let uu____19108 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____19108.FStar_Syntax_Syntax.n  in
                            (match uu____19107 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19126 ->
                                 let uu____19127 =
                                   let uu____19128 = is_cons head1  in
                                   Prims.op_Negation uu____19128  in
                                 FStar_Util.Inr uu____19127))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19197)::rest_a,(p1,uu____19200)::rest_p) ->
                       let uu____19244 = matches_pat t2 p1  in
                       (match uu____19244 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19293 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19399 = matches_pat scrutinee1 p1  in
                       (match uu____19399 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19439  ->
                                  let uu____19440 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____19441 =
                                    let uu____19442 =
                                      FStar_List.map
                                        (fun uu____19452  ->
                                           match uu____19452 with
                                           | (uu____19457,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____19442
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19440 uu____19441);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19488  ->
                                       match uu____19488 with
                                       | (bv,t2) ->
                                           let uu____19511 =
                                             let uu____19518 =
                                               let uu____19521 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____19521
                                                in
                                             let uu____19522 =
                                               let uu____19523 =
                                                 let uu____19554 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____19554, false)
                                                  in
                                               Clos uu____19523  in
                                             (uu____19518, uu____19522)  in
                                           uu____19511 :: env2) env1 s
                                 in
                              let uu____19671 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____19671)))
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
             (fun uu___87_19692  ->
                match uu___87_19692 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19696 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19702 -> d  in
      let uu____19705 = to_fsteps s  in
      let uu____19706 =
        let uu____19707 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
        let uu____19708 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
        let uu____19709 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
        let uu____19710 =
          FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
           in
        let uu____19711 =
          FStar_TypeChecker_Env.debug e
            (FStar_Options.Other "print_normalized_terms")
           in
        {
          gen = uu____19707;
          primop = uu____19708;
          b380 = uu____19709;
          norm_delayed = uu____19710;
          print_normalized = uu____19711
        }  in
      let uu____19712 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____19714 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations)
              in
           Prims.op_Negation uu____19714)
         in
      {
        steps = uu____19705;
        tcenv = e;
        debug = uu____19706;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____19712
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
            let uu___182_19739 = config s e  in
            {
              steps = (uu___182_19739.steps);
              tcenv = (uu___182_19739.tcenv);
              debug = (uu___182_19739.debug);
              delta_level = (uu___182_19739.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___182_19739.strong);
              memoize_lazy = (uu___182_19739.memoize_lazy);
              normalize_pure_lets = (uu___182_19739.normalize_pure_lets)
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
      fun t  -> let uu____19764 = config s e  in norm_comp uu____19764 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____19777 = config [] env  in norm_universe uu____19777 [] u
  
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
        let uu____19795 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19795  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____19802 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_19821 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_19821.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_19821.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____19828 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____19828
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
                  let uu___184_19837 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_19837.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_19837.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_19837.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_19839 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_19839.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_19839.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_19839.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_19839.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_19840 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_19840.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_19840.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____19842 -> c
  
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
        let uu____19854 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19854  in
      let uu____19861 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____19861
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____19865  ->
                 let uu____19866 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____19866)
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
            ((let uu____19883 =
                let uu____19888 =
                  let uu____19889 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19889
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19888)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____19883);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19900 = config [AllowUnboundUniverses] env  in
          norm_comp uu____19900 [] c
        with
        | e ->
            ((let uu____19913 =
                let uu____19918 =
                  let uu____19919 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19919
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19918)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____19913);
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
                   let uu____19956 =
                     let uu____19957 =
                       let uu____19964 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____19964)  in
                     FStar_Syntax_Syntax.Tm_refine uu____19957  in
                   mk uu____19956 t01.FStar_Syntax_Syntax.pos
               | uu____19969 -> t2)
          | uu____19970 -> t2  in
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
        let uu____20010 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____20010 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____20039 ->
                 let uu____20046 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____20046 with
                  | (actuals,uu____20056,uu____20057) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____20071 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____20071 with
                         | (binders,args) ->
                             let uu____20088 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____20088
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
      | uu____20096 ->
          let uu____20097 = FStar_Syntax_Util.head_and_args t  in
          (match uu____20097 with
           | (head1,args) ->
               let uu____20134 =
                 let uu____20135 = FStar_Syntax_Subst.compress head1  in
                 uu____20135.FStar_Syntax_Syntax.n  in
               (match uu____20134 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20138,thead) ->
                    let uu____20164 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____20164 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20206 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_20214 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_20214.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_20214.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_20214.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_20214.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_20214.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_20214.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_20214.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_20214.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_20214.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_20214.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_20214.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_20214.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_20214.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_20214.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_20214.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_20214.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_20214.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_20214.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_20214.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_20214.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_20214.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_20214.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_20214.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_20214.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___191_20214.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_20214.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___191_20214.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_20214.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_20214.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_20214.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_20214.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_20214.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____20206 with
                            | (uu____20215,ty,uu____20217) ->
                                eta_expand_with_type env t ty))
                | uu____20218 ->
                    let uu____20219 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_20227 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_20227.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_20227.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_20227.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_20227.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_20227.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_20227.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_20227.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_20227.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_20227.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_20227.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_20227.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_20227.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_20227.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_20227.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_20227.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_20227.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_20227.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_20227.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_20227.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_20227.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_20227.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_20227.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_20227.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_20227.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___192_20227.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_20227.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___192_20227.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_20227.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_20227.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_20227.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_20227.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_20227.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____20219 with
                     | (uu____20228,ty,uu____20230) ->
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
      let uu___193_20287 = x  in
      let uu____20288 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_20287.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_20287.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20288
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20291 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20316 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20317 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20318 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20319 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20326 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20327 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_20355 = rc  in
          let uu____20356 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____20363 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_20355.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20356;
            FStar_Syntax_Syntax.residual_flags = uu____20363
          }  in
        let uu____20366 =
          let uu____20367 =
            let uu____20384 = elim_delayed_subst_binders bs  in
            let uu____20391 = elim_delayed_subst_term t2  in
            let uu____20392 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____20384, uu____20391, uu____20392)  in
          FStar_Syntax_Syntax.Tm_abs uu____20367  in
        mk1 uu____20366
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____20421 =
          let uu____20422 =
            let uu____20435 = elim_delayed_subst_binders bs  in
            let uu____20442 = elim_delayed_subst_comp c  in
            (uu____20435, uu____20442)  in
          FStar_Syntax_Syntax.Tm_arrow uu____20422  in
        mk1 uu____20421
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____20455 =
          let uu____20456 =
            let uu____20463 = elim_bv bv  in
            let uu____20464 = elim_delayed_subst_term phi  in
            (uu____20463, uu____20464)  in
          FStar_Syntax_Syntax.Tm_refine uu____20456  in
        mk1 uu____20455
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____20487 =
          let uu____20488 =
            let uu____20503 = elim_delayed_subst_term t2  in
            let uu____20504 = elim_delayed_subst_args args  in
            (uu____20503, uu____20504)  in
          FStar_Syntax_Syntax.Tm_app uu____20488  in
        mk1 uu____20487
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_20568 = p  in
              let uu____20569 =
                let uu____20570 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____20570  in
              {
                FStar_Syntax_Syntax.v = uu____20569;
                FStar_Syntax_Syntax.p =
                  (uu___195_20568.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_20572 = p  in
              let uu____20573 =
                let uu____20574 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____20574  in
              {
                FStar_Syntax_Syntax.v = uu____20573;
                FStar_Syntax_Syntax.p =
                  (uu___196_20572.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_20581 = p  in
              let uu____20582 =
                let uu____20583 =
                  let uu____20590 = elim_bv x  in
                  let uu____20591 = elim_delayed_subst_term t0  in
                  (uu____20590, uu____20591)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____20583  in
              {
                FStar_Syntax_Syntax.v = uu____20582;
                FStar_Syntax_Syntax.p =
                  (uu___197_20581.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_20610 = p  in
              let uu____20611 =
                let uu____20612 =
                  let uu____20625 =
                    FStar_List.map
                      (fun uu____20648  ->
                         match uu____20648 with
                         | (x,b) ->
                             let uu____20661 = elim_pat x  in
                             (uu____20661, b)) pats
                     in
                  (fv, uu____20625)  in
                FStar_Syntax_Syntax.Pat_cons uu____20612  in
              {
                FStar_Syntax_Syntax.v = uu____20611;
                FStar_Syntax_Syntax.p =
                  (uu___198_20610.FStar_Syntax_Syntax.p)
              }
          | uu____20674 -> p  in
        let elim_branch uu____20696 =
          match uu____20696 with
          | (pat,wopt,t3) ->
              let uu____20722 = elim_pat pat  in
              let uu____20725 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____20728 = elim_delayed_subst_term t3  in
              (uu____20722, uu____20725, uu____20728)
           in
        let uu____20733 =
          let uu____20734 =
            let uu____20757 = elim_delayed_subst_term t2  in
            let uu____20758 = FStar_List.map elim_branch branches  in
            (uu____20757, uu____20758)  in
          FStar_Syntax_Syntax.Tm_match uu____20734  in
        mk1 uu____20733
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____20867 =
          match uu____20867 with
          | (tc,topt) ->
              let uu____20902 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____20912 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____20912
                | FStar_Util.Inr c ->
                    let uu____20914 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____20914
                 in
              let uu____20915 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____20902, uu____20915)
           in
        let uu____20924 =
          let uu____20925 =
            let uu____20952 = elim_delayed_subst_term t2  in
            let uu____20953 = elim_ascription a  in
            (uu____20952, uu____20953, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____20925  in
        mk1 uu____20924
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_20998 = lb  in
          let uu____20999 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____21002 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_20998.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_20998.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____20999;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_20998.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____21002
          }  in
        let uu____21005 =
          let uu____21006 =
            let uu____21019 =
              let uu____21026 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____21026)  in
            let uu____21035 = elim_delayed_subst_term t2  in
            (uu____21019, uu____21035)  in
          FStar_Syntax_Syntax.Tm_let uu____21006  in
        mk1 uu____21005
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____21068 =
          let uu____21069 =
            let uu____21086 = elim_delayed_subst_term t2  in
            (uv, uu____21086)  in
          FStar_Syntax_Syntax.Tm_uvar uu____21069  in
        mk1 uu____21068
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21103 =
          let uu____21104 =
            let uu____21111 = elim_delayed_subst_term t2  in
            let uu____21112 = elim_delayed_subst_meta md  in
            (uu____21111, uu____21112)  in
          FStar_Syntax_Syntax.Tm_meta uu____21104  in
        mk1 uu____21103

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___88_21119  ->
         match uu___88_21119 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21123 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____21123
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
        let uu____21144 =
          let uu____21145 =
            let uu____21154 = elim_delayed_subst_term t  in
            (uu____21154, uopt)  in
          FStar_Syntax_Syntax.Total uu____21145  in
        mk1 uu____21144
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21167 =
          let uu____21168 =
            let uu____21177 = elim_delayed_subst_term t  in
            (uu____21177, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____21168  in
        mk1 uu____21167
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_21182 = ct  in
          let uu____21183 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____21186 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____21195 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_21182.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_21182.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21183;
            FStar_Syntax_Syntax.effect_args = uu____21186;
            FStar_Syntax_Syntax.flags = uu____21195
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___89_21198  ->
    match uu___89_21198 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21210 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____21210
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21243 =
          let uu____21250 = elim_delayed_subst_term t  in (m, uu____21250)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____21243
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21258 =
          let uu____21267 = elim_delayed_subst_term t  in
          (m1, m2, uu____21267)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21258
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21275 =
          let uu____21284 = elim_delayed_subst_term t  in (d, s, uu____21284)
           in
        FStar_Syntax_Syntax.Meta_alien uu____21275
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____21307  ->
         match uu____21307 with
         | (t,q) ->
             let uu____21318 = elim_delayed_subst_term t  in (uu____21318, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21338  ->
         match uu____21338 with
         | (x,q) ->
             let uu____21349 =
               let uu___201_21350 = x  in
               let uu____21351 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_21350.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_21350.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21351
               }  in
             (uu____21349, q)) bs

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
            | (uu____21427,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____21433,FStar_Util.Inl t) ->
                let uu____21439 =
                  let uu____21442 =
                    let uu____21443 =
                      let uu____21456 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____21456)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____21443  in
                  FStar_Syntax_Syntax.mk uu____21442  in
                uu____21439 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____21460 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____21460 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____21488 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____21543 ->
                    let uu____21544 =
                      let uu____21553 =
                        let uu____21554 = FStar_Syntax_Subst.compress t4  in
                        uu____21554.FStar_Syntax_Syntax.n  in
                      (uu____21553, tc)  in
                    (match uu____21544 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____21579) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____21616) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____21655,FStar_Util.Inl uu____21656) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____21679 -> failwith "Impossible")
                 in
              (match uu____21488 with
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
          let uu____21784 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____21784 with
          | (univ_names1,binders1,tc) ->
              let uu____21842 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____21842)
  
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
          let uu____21877 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____21877 with
          | (univ_names1,binders1,tc) ->
              let uu____21937 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____21937)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____21970 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____21970 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_21998 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_21998.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_21998.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_21998.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_21998.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_22019 = s  in
          let uu____22020 =
            let uu____22021 =
              let uu____22030 = FStar_List.map (elim_uvars env) sigs  in
              (uu____22030, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____22021  in
          {
            FStar_Syntax_Syntax.sigel = uu____22020;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_22019.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_22019.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_22019.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_22019.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____22047 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22047 with
           | (univ_names1,uu____22065,typ1) ->
               let uu___204_22079 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_22079.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_22079.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_22079.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_22079.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22085 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22085 with
           | (univ_names1,uu____22103,typ1) ->
               let uu___205_22117 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_22117.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_22117.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_22117.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_22117.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22151 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____22151 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22174 =
                            let uu____22175 =
                              let uu____22176 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____22176  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22175
                             in
                          elim_delayed_subst_term uu____22174  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_22179 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_22179.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_22179.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___207_22180 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_22180.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_22180.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_22180.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_22180.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_22192 = s  in
          let uu____22193 =
            let uu____22194 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____22194  in
          {
            FStar_Syntax_Syntax.sigel = uu____22193;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_22192.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_22192.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_22192.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_22192.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22198 = elim_uvars_aux_t env us [] t  in
          (match uu____22198 with
           | (us1,uu____22216,t1) ->
               let uu___209_22230 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_22230.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_22230.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_22230.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_22230.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22231 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22233 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____22233 with
           | (univs1,binders,signature) ->
               let uu____22261 =
                 let uu____22270 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____22270 with
                 | (univs_opening,univs2) ->
                     let uu____22297 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____22297)
                  in
               (match uu____22261 with
                | (univs_opening,univs_closing) ->
                    let uu____22314 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____22320 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____22321 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____22320, uu____22321)  in
                    (match uu____22314 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____22343 =
                           match uu____22343 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____22361 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____22361 with
                                | (us1,t1) ->
                                    let uu____22372 =
                                      let uu____22377 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____22384 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____22377, uu____22384)  in
                                    (match uu____22372 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____22397 =
                                           let uu____22402 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____22411 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____22402, uu____22411)  in
                                         (match uu____22397 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____22427 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____22427
                                                 in
                                              let uu____22428 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____22428 with
                                               | (uu____22449,uu____22450,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____22465 =
                                                       let uu____22466 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____22466
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____22465
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____22471 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____22471 with
                           | (uu____22484,uu____22485,t1) -> t1  in
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
                             | uu____22545 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____22562 =
                               let uu____22563 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____22563.FStar_Syntax_Syntax.n  in
                             match uu____22562 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____22622 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____22651 =
                               let uu____22652 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____22652.FStar_Syntax_Syntax.n  in
                             match uu____22651 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____22673) ->
                                 let uu____22694 = destruct_action_body body
                                    in
                                 (match uu____22694 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____22739 ->
                                 let uu____22740 = destruct_action_body t  in
                                 (match uu____22740 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____22789 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____22789 with
                           | (action_univs,t) ->
                               let uu____22798 = destruct_action_typ_templ t
                                  in
                               (match uu____22798 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_22839 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_22839.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_22839.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___211_22841 = ed  in
                           let uu____22842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____22843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____22844 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____22845 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____22846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____22847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____22848 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____22849 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____22850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____22851 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____22852 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____22853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____22854 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____22855 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_22841.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_22841.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____22842;
                             FStar_Syntax_Syntax.bind_wp = uu____22843;
                             FStar_Syntax_Syntax.if_then_else = uu____22844;
                             FStar_Syntax_Syntax.ite_wp = uu____22845;
                             FStar_Syntax_Syntax.stronger = uu____22846;
                             FStar_Syntax_Syntax.close_wp = uu____22847;
                             FStar_Syntax_Syntax.assert_p = uu____22848;
                             FStar_Syntax_Syntax.assume_p = uu____22849;
                             FStar_Syntax_Syntax.null_wp = uu____22850;
                             FStar_Syntax_Syntax.trivial = uu____22851;
                             FStar_Syntax_Syntax.repr = uu____22852;
                             FStar_Syntax_Syntax.return_repr = uu____22853;
                             FStar_Syntax_Syntax.bind_repr = uu____22854;
                             FStar_Syntax_Syntax.actions = uu____22855
                           }  in
                         let uu___212_22858 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_22858.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_22858.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_22858.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_22858.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___90_22875 =
            match uu___90_22875 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____22902 = elim_uvars_aux_t env us [] t  in
                (match uu____22902 with
                 | (us1,uu____22926,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_22945 = sub_eff  in
            let uu____22946 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____22949 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_22945.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_22945.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____22946;
              FStar_Syntax_Syntax.lift = uu____22949
            }  in
          let uu___214_22952 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_22952.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_22952.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_22952.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_22952.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____22962 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____22962 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_22996 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_22996.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_22996.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_22996.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_22996.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____23007 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  