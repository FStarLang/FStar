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
  | DoNotUnfoldPureLets 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____30 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____36 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____42 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____49 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____62 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____68 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____74 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____80 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____86 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____92 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____99 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____115 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____137 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____157 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____170 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____176 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____182 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____188 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____194 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____200 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____206 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____212 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____218 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____224 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____230 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____243 'Auu____244 .
    ('Auu____243 -> 'Auu____244) ->
      'Auu____244 ->
        'Auu____243 FStar_Pervasives_Native.option -> 'Auu____244
  =
  fun f  ->
    fun d  ->
      fun uu___77_264  ->
        match uu___77_264 with
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
  do_not_unfold_pure_lets: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_fully: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
  unascribe: Prims.bool ;
  in_full_norm_request: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__primops
  
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__do_not_unfold_pure_lets
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unfold_fully
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__unascribe
  
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__in_full_norm_request
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
    unfold_fully = FStar_Pervasives_Native.None;
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
    unascribe = false;
    in_full_norm_request = false
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___78_1404 =
        match uu___78_1404 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1424 = fs  in
          {
            beta = true;
            iota = (uu___96_1424.iota);
            zeta = (uu___96_1424.zeta);
            weak = (uu___96_1424.weak);
            hnf = (uu___96_1424.hnf);
            primops = (uu___96_1424.primops);
            do_not_unfold_pure_lets = (uu___96_1424.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1424.unfold_until);
            unfold_only = (uu___96_1424.unfold_only);
            unfold_fully = (uu___96_1424.unfold_fully);
            unfold_attr = (uu___96_1424.unfold_attr);
            unfold_tac = (uu___96_1424.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1424.pure_subterms_within_computations);
            simplify = (uu___96_1424.simplify);
            erase_universes = (uu___96_1424.erase_universes);
            allow_unbound_universes = (uu___96_1424.allow_unbound_universes);
            reify_ = (uu___96_1424.reify_);
            compress_uvars = (uu___96_1424.compress_uvars);
            no_full_norm = (uu___96_1424.no_full_norm);
            check_no_uvars = (uu___96_1424.check_no_uvars);
            unmeta = (uu___96_1424.unmeta);
            unascribe = (uu___96_1424.unascribe);
            in_full_norm_request = (uu___96_1424.in_full_norm_request)
          }
      | Iota  ->
          let uu___97_1425 = fs  in
          {
            beta = (uu___97_1425.beta);
            iota = true;
            zeta = (uu___97_1425.zeta);
            weak = (uu___97_1425.weak);
            hnf = (uu___97_1425.hnf);
            primops = (uu___97_1425.primops);
            do_not_unfold_pure_lets = (uu___97_1425.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1425.unfold_until);
            unfold_only = (uu___97_1425.unfold_only);
            unfold_fully = (uu___97_1425.unfold_fully);
            unfold_attr = (uu___97_1425.unfold_attr);
            unfold_tac = (uu___97_1425.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1425.pure_subterms_within_computations);
            simplify = (uu___97_1425.simplify);
            erase_universes = (uu___97_1425.erase_universes);
            allow_unbound_universes = (uu___97_1425.allow_unbound_universes);
            reify_ = (uu___97_1425.reify_);
            compress_uvars = (uu___97_1425.compress_uvars);
            no_full_norm = (uu___97_1425.no_full_norm);
            check_no_uvars = (uu___97_1425.check_no_uvars);
            unmeta = (uu___97_1425.unmeta);
            unascribe = (uu___97_1425.unascribe);
            in_full_norm_request = (uu___97_1425.in_full_norm_request)
          }
      | Zeta  ->
          let uu___98_1426 = fs  in
          {
            beta = (uu___98_1426.beta);
            iota = (uu___98_1426.iota);
            zeta = true;
            weak = (uu___98_1426.weak);
            hnf = (uu___98_1426.hnf);
            primops = (uu___98_1426.primops);
            do_not_unfold_pure_lets = (uu___98_1426.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1426.unfold_until);
            unfold_only = (uu___98_1426.unfold_only);
            unfold_fully = (uu___98_1426.unfold_fully);
            unfold_attr = (uu___98_1426.unfold_attr);
            unfold_tac = (uu___98_1426.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1426.pure_subterms_within_computations);
            simplify = (uu___98_1426.simplify);
            erase_universes = (uu___98_1426.erase_universes);
            allow_unbound_universes = (uu___98_1426.allow_unbound_universes);
            reify_ = (uu___98_1426.reify_);
            compress_uvars = (uu___98_1426.compress_uvars);
            no_full_norm = (uu___98_1426.no_full_norm);
            check_no_uvars = (uu___98_1426.check_no_uvars);
            unmeta = (uu___98_1426.unmeta);
            unascribe = (uu___98_1426.unascribe);
            in_full_norm_request = (uu___98_1426.in_full_norm_request)
          }
      | Exclude (Beta ) ->
          let uu___99_1427 = fs  in
          {
            beta = false;
            iota = (uu___99_1427.iota);
            zeta = (uu___99_1427.zeta);
            weak = (uu___99_1427.weak);
            hnf = (uu___99_1427.hnf);
            primops = (uu___99_1427.primops);
            do_not_unfold_pure_lets = (uu___99_1427.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1427.unfold_until);
            unfold_only = (uu___99_1427.unfold_only);
            unfold_fully = (uu___99_1427.unfold_fully);
            unfold_attr = (uu___99_1427.unfold_attr);
            unfold_tac = (uu___99_1427.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1427.pure_subterms_within_computations);
            simplify = (uu___99_1427.simplify);
            erase_universes = (uu___99_1427.erase_universes);
            allow_unbound_universes = (uu___99_1427.allow_unbound_universes);
            reify_ = (uu___99_1427.reify_);
            compress_uvars = (uu___99_1427.compress_uvars);
            no_full_norm = (uu___99_1427.no_full_norm);
            check_no_uvars = (uu___99_1427.check_no_uvars);
            unmeta = (uu___99_1427.unmeta);
            unascribe = (uu___99_1427.unascribe);
            in_full_norm_request = (uu___99_1427.in_full_norm_request)
          }
      | Exclude (Iota ) ->
          let uu___100_1428 = fs  in
          {
            beta = (uu___100_1428.beta);
            iota = false;
            zeta = (uu___100_1428.zeta);
            weak = (uu___100_1428.weak);
            hnf = (uu___100_1428.hnf);
            primops = (uu___100_1428.primops);
            do_not_unfold_pure_lets = (uu___100_1428.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1428.unfold_until);
            unfold_only = (uu___100_1428.unfold_only);
            unfold_fully = (uu___100_1428.unfold_fully);
            unfold_attr = (uu___100_1428.unfold_attr);
            unfold_tac = (uu___100_1428.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1428.pure_subterms_within_computations);
            simplify = (uu___100_1428.simplify);
            erase_universes = (uu___100_1428.erase_universes);
            allow_unbound_universes = (uu___100_1428.allow_unbound_universes);
            reify_ = (uu___100_1428.reify_);
            compress_uvars = (uu___100_1428.compress_uvars);
            no_full_norm = (uu___100_1428.no_full_norm);
            check_no_uvars = (uu___100_1428.check_no_uvars);
            unmeta = (uu___100_1428.unmeta);
            unascribe = (uu___100_1428.unascribe);
            in_full_norm_request = (uu___100_1428.in_full_norm_request)
          }
      | Exclude (Zeta ) ->
          let uu___101_1429 = fs  in
          {
            beta = (uu___101_1429.beta);
            iota = (uu___101_1429.iota);
            zeta = false;
            weak = (uu___101_1429.weak);
            hnf = (uu___101_1429.hnf);
            primops = (uu___101_1429.primops);
            do_not_unfold_pure_lets = (uu___101_1429.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1429.unfold_until);
            unfold_only = (uu___101_1429.unfold_only);
            unfold_fully = (uu___101_1429.unfold_fully);
            unfold_attr = (uu___101_1429.unfold_attr);
            unfold_tac = (uu___101_1429.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1429.pure_subterms_within_computations);
            simplify = (uu___101_1429.simplify);
            erase_universes = (uu___101_1429.erase_universes);
            allow_unbound_universes = (uu___101_1429.allow_unbound_universes);
            reify_ = (uu___101_1429.reify_);
            compress_uvars = (uu___101_1429.compress_uvars);
            no_full_norm = (uu___101_1429.no_full_norm);
            check_no_uvars = (uu___101_1429.check_no_uvars);
            unmeta = (uu___101_1429.unmeta);
            unascribe = (uu___101_1429.unascribe);
            in_full_norm_request = (uu___101_1429.in_full_norm_request)
          }
      | Exclude uu____1430 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1431 = fs  in
          {
            beta = (uu___102_1431.beta);
            iota = (uu___102_1431.iota);
            zeta = (uu___102_1431.zeta);
            weak = true;
            hnf = (uu___102_1431.hnf);
            primops = (uu___102_1431.primops);
            do_not_unfold_pure_lets = (uu___102_1431.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1431.unfold_until);
            unfold_only = (uu___102_1431.unfold_only);
            unfold_fully = (uu___102_1431.unfold_fully);
            unfold_attr = (uu___102_1431.unfold_attr);
            unfold_tac = (uu___102_1431.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1431.pure_subterms_within_computations);
            simplify = (uu___102_1431.simplify);
            erase_universes = (uu___102_1431.erase_universes);
            allow_unbound_universes = (uu___102_1431.allow_unbound_universes);
            reify_ = (uu___102_1431.reify_);
            compress_uvars = (uu___102_1431.compress_uvars);
            no_full_norm = (uu___102_1431.no_full_norm);
            check_no_uvars = (uu___102_1431.check_no_uvars);
            unmeta = (uu___102_1431.unmeta);
            unascribe = (uu___102_1431.unascribe);
            in_full_norm_request = (uu___102_1431.in_full_norm_request)
          }
      | HNF  ->
          let uu___103_1432 = fs  in
          {
            beta = (uu___103_1432.beta);
            iota = (uu___103_1432.iota);
            zeta = (uu___103_1432.zeta);
            weak = (uu___103_1432.weak);
            hnf = true;
            primops = (uu___103_1432.primops);
            do_not_unfold_pure_lets = (uu___103_1432.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1432.unfold_until);
            unfold_only = (uu___103_1432.unfold_only);
            unfold_fully = (uu___103_1432.unfold_fully);
            unfold_attr = (uu___103_1432.unfold_attr);
            unfold_tac = (uu___103_1432.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1432.pure_subterms_within_computations);
            simplify = (uu___103_1432.simplify);
            erase_universes = (uu___103_1432.erase_universes);
            allow_unbound_universes = (uu___103_1432.allow_unbound_universes);
            reify_ = (uu___103_1432.reify_);
            compress_uvars = (uu___103_1432.compress_uvars);
            no_full_norm = (uu___103_1432.no_full_norm);
            check_no_uvars = (uu___103_1432.check_no_uvars);
            unmeta = (uu___103_1432.unmeta);
            unascribe = (uu___103_1432.unascribe);
            in_full_norm_request = (uu___103_1432.in_full_norm_request)
          }
      | Primops  ->
          let uu___104_1433 = fs  in
          {
            beta = (uu___104_1433.beta);
            iota = (uu___104_1433.iota);
            zeta = (uu___104_1433.zeta);
            weak = (uu___104_1433.weak);
            hnf = (uu___104_1433.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1433.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1433.unfold_until);
            unfold_only = (uu___104_1433.unfold_only);
            unfold_fully = (uu___104_1433.unfold_fully);
            unfold_attr = (uu___104_1433.unfold_attr);
            unfold_tac = (uu___104_1433.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1433.pure_subterms_within_computations);
            simplify = (uu___104_1433.simplify);
            erase_universes = (uu___104_1433.erase_universes);
            allow_unbound_universes = (uu___104_1433.allow_unbound_universes);
            reify_ = (uu___104_1433.reify_);
            compress_uvars = (uu___104_1433.compress_uvars);
            no_full_norm = (uu___104_1433.no_full_norm);
            check_no_uvars = (uu___104_1433.check_no_uvars);
            unmeta = (uu___104_1433.unmeta);
            unascribe = (uu___104_1433.unascribe);
            in_full_norm_request = (uu___104_1433.in_full_norm_request)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1434 = fs  in
          {
            beta = (uu___105_1434.beta);
            iota = (uu___105_1434.iota);
            zeta = (uu___105_1434.zeta);
            weak = (uu___105_1434.weak);
            hnf = (uu___105_1434.hnf);
            primops = (uu___105_1434.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1434.unfold_until);
            unfold_only = (uu___105_1434.unfold_only);
            unfold_fully = (uu___105_1434.unfold_fully);
            unfold_attr = (uu___105_1434.unfold_attr);
            unfold_tac = (uu___105_1434.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1434.pure_subterms_within_computations);
            simplify = (uu___105_1434.simplify);
            erase_universes = (uu___105_1434.erase_universes);
            allow_unbound_universes = (uu___105_1434.allow_unbound_universes);
            reify_ = (uu___105_1434.reify_);
            compress_uvars = (uu___105_1434.compress_uvars);
            no_full_norm = (uu___105_1434.no_full_norm);
            check_no_uvars = (uu___105_1434.check_no_uvars);
            unmeta = (uu___105_1434.unmeta);
            unascribe = (uu___105_1434.unascribe);
            in_full_norm_request = (uu___105_1434.in_full_norm_request)
          }
      | UnfoldUntil d ->
          let uu___106_1436 = fs  in
          {
            beta = (uu___106_1436.beta);
            iota = (uu___106_1436.iota);
            zeta = (uu___106_1436.zeta);
            weak = (uu___106_1436.weak);
            hnf = (uu___106_1436.hnf);
            primops = (uu___106_1436.primops);
            do_not_unfold_pure_lets = (uu___106_1436.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1436.unfold_only);
            unfold_fully = (uu___106_1436.unfold_fully);
            unfold_attr = (uu___106_1436.unfold_attr);
            unfold_tac = (uu___106_1436.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1436.pure_subterms_within_computations);
            simplify = (uu___106_1436.simplify);
            erase_universes = (uu___106_1436.erase_universes);
            allow_unbound_universes = (uu___106_1436.allow_unbound_universes);
            reify_ = (uu___106_1436.reify_);
            compress_uvars = (uu___106_1436.compress_uvars);
            no_full_norm = (uu___106_1436.no_full_norm);
            check_no_uvars = (uu___106_1436.check_no_uvars);
            unmeta = (uu___106_1436.unmeta);
            unascribe = (uu___106_1436.unascribe);
            in_full_norm_request = (uu___106_1436.in_full_norm_request)
          }
      | UnfoldOnly lids ->
          let uu___107_1440 = fs  in
          {
            beta = (uu___107_1440.beta);
            iota = (uu___107_1440.iota);
            zeta = (uu___107_1440.zeta);
            weak = (uu___107_1440.weak);
            hnf = (uu___107_1440.hnf);
            primops = (uu___107_1440.primops);
            do_not_unfold_pure_lets = (uu___107_1440.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1440.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1440.unfold_fully);
            unfold_attr = (uu___107_1440.unfold_attr);
            unfold_tac = (uu___107_1440.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1440.pure_subterms_within_computations);
            simplify = (uu___107_1440.simplify);
            erase_universes = (uu___107_1440.erase_universes);
            allow_unbound_universes = (uu___107_1440.allow_unbound_universes);
            reify_ = (uu___107_1440.reify_);
            compress_uvars = (uu___107_1440.compress_uvars);
            no_full_norm = (uu___107_1440.no_full_norm);
            check_no_uvars = (uu___107_1440.check_no_uvars);
            unmeta = (uu___107_1440.unmeta);
            unascribe = (uu___107_1440.unascribe);
            in_full_norm_request = (uu___107_1440.in_full_norm_request)
          }
      | UnfoldFully lids ->
          let uu___108_1446 = fs  in
          {
            beta = (uu___108_1446.beta);
            iota = (uu___108_1446.iota);
            zeta = (uu___108_1446.zeta);
            weak = (uu___108_1446.weak);
            hnf = (uu___108_1446.hnf);
            primops = (uu___108_1446.primops);
            do_not_unfold_pure_lets = (uu___108_1446.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1446.unfold_until);
            unfold_only = (uu___108_1446.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1446.unfold_attr);
            unfold_tac = (uu___108_1446.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1446.pure_subterms_within_computations);
            simplify = (uu___108_1446.simplify);
            erase_universes = (uu___108_1446.erase_universes);
            allow_unbound_universes = (uu___108_1446.allow_unbound_universes);
            reify_ = (uu___108_1446.reify_);
            compress_uvars = (uu___108_1446.compress_uvars);
            no_full_norm = (uu___108_1446.no_full_norm);
            check_no_uvars = (uu___108_1446.check_no_uvars);
            unmeta = (uu___108_1446.unmeta);
            unascribe = (uu___108_1446.unascribe);
            in_full_norm_request = (uu___108_1446.in_full_norm_request)
          }
      | UnfoldAttr attr ->
          let uu___109_1450 = fs  in
          {
            beta = (uu___109_1450.beta);
            iota = (uu___109_1450.iota);
            zeta = (uu___109_1450.zeta);
            weak = (uu___109_1450.weak);
            hnf = (uu___109_1450.hnf);
            primops = (uu___109_1450.primops);
            do_not_unfold_pure_lets = (uu___109_1450.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1450.unfold_until);
            unfold_only = (uu___109_1450.unfold_only);
            unfold_fully = (uu___109_1450.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1450.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1450.pure_subterms_within_computations);
            simplify = (uu___109_1450.simplify);
            erase_universes = (uu___109_1450.erase_universes);
            allow_unbound_universes = (uu___109_1450.allow_unbound_universes);
            reify_ = (uu___109_1450.reify_);
            compress_uvars = (uu___109_1450.compress_uvars);
            no_full_norm = (uu___109_1450.no_full_norm);
            check_no_uvars = (uu___109_1450.check_no_uvars);
            unmeta = (uu___109_1450.unmeta);
            unascribe = (uu___109_1450.unascribe);
            in_full_norm_request = (uu___109_1450.in_full_norm_request)
          }
      | UnfoldTac  ->
          let uu___110_1451 = fs  in
          {
            beta = (uu___110_1451.beta);
            iota = (uu___110_1451.iota);
            zeta = (uu___110_1451.zeta);
            weak = (uu___110_1451.weak);
            hnf = (uu___110_1451.hnf);
            primops = (uu___110_1451.primops);
            do_not_unfold_pure_lets = (uu___110_1451.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1451.unfold_until);
            unfold_only = (uu___110_1451.unfold_only);
            unfold_fully = (uu___110_1451.unfold_fully);
            unfold_attr = (uu___110_1451.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1451.pure_subterms_within_computations);
            simplify = (uu___110_1451.simplify);
            erase_universes = (uu___110_1451.erase_universes);
            allow_unbound_universes = (uu___110_1451.allow_unbound_universes);
            reify_ = (uu___110_1451.reify_);
            compress_uvars = (uu___110_1451.compress_uvars);
            no_full_norm = (uu___110_1451.no_full_norm);
            check_no_uvars = (uu___110_1451.check_no_uvars);
            unmeta = (uu___110_1451.unmeta);
            unascribe = (uu___110_1451.unascribe);
            in_full_norm_request = (uu___110_1451.in_full_norm_request)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1452 = fs  in
          {
            beta = (uu___111_1452.beta);
            iota = (uu___111_1452.iota);
            zeta = (uu___111_1452.zeta);
            weak = (uu___111_1452.weak);
            hnf = (uu___111_1452.hnf);
            primops = (uu___111_1452.primops);
            do_not_unfold_pure_lets = (uu___111_1452.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1452.unfold_until);
            unfold_only = (uu___111_1452.unfold_only);
            unfold_fully = (uu___111_1452.unfold_fully);
            unfold_attr = (uu___111_1452.unfold_attr);
            unfold_tac = (uu___111_1452.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1452.simplify);
            erase_universes = (uu___111_1452.erase_universes);
            allow_unbound_universes = (uu___111_1452.allow_unbound_universes);
            reify_ = (uu___111_1452.reify_);
            compress_uvars = (uu___111_1452.compress_uvars);
            no_full_norm = (uu___111_1452.no_full_norm);
            check_no_uvars = (uu___111_1452.check_no_uvars);
            unmeta = (uu___111_1452.unmeta);
            unascribe = (uu___111_1452.unascribe);
            in_full_norm_request = (uu___111_1452.in_full_norm_request)
          }
      | Simplify  ->
          let uu___112_1453 = fs  in
          {
            beta = (uu___112_1453.beta);
            iota = (uu___112_1453.iota);
            zeta = (uu___112_1453.zeta);
            weak = (uu___112_1453.weak);
            hnf = (uu___112_1453.hnf);
            primops = (uu___112_1453.primops);
            do_not_unfold_pure_lets = (uu___112_1453.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1453.unfold_until);
            unfold_only = (uu___112_1453.unfold_only);
            unfold_fully = (uu___112_1453.unfold_fully);
            unfold_attr = (uu___112_1453.unfold_attr);
            unfold_tac = (uu___112_1453.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1453.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1453.erase_universes);
            allow_unbound_universes = (uu___112_1453.allow_unbound_universes);
            reify_ = (uu___112_1453.reify_);
            compress_uvars = (uu___112_1453.compress_uvars);
            no_full_norm = (uu___112_1453.no_full_norm);
            check_no_uvars = (uu___112_1453.check_no_uvars);
            unmeta = (uu___112_1453.unmeta);
            unascribe = (uu___112_1453.unascribe);
            in_full_norm_request = (uu___112_1453.in_full_norm_request)
          }
      | EraseUniverses  ->
          let uu___113_1454 = fs  in
          {
            beta = (uu___113_1454.beta);
            iota = (uu___113_1454.iota);
            zeta = (uu___113_1454.zeta);
            weak = (uu___113_1454.weak);
            hnf = (uu___113_1454.hnf);
            primops = (uu___113_1454.primops);
            do_not_unfold_pure_lets = (uu___113_1454.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1454.unfold_until);
            unfold_only = (uu___113_1454.unfold_only);
            unfold_fully = (uu___113_1454.unfold_fully);
            unfold_attr = (uu___113_1454.unfold_attr);
            unfold_tac = (uu___113_1454.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1454.pure_subterms_within_computations);
            simplify = (uu___113_1454.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1454.allow_unbound_universes);
            reify_ = (uu___113_1454.reify_);
            compress_uvars = (uu___113_1454.compress_uvars);
            no_full_norm = (uu___113_1454.no_full_norm);
            check_no_uvars = (uu___113_1454.check_no_uvars);
            unmeta = (uu___113_1454.unmeta);
            unascribe = (uu___113_1454.unascribe);
            in_full_norm_request = (uu___113_1454.in_full_norm_request)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1455 = fs  in
          {
            beta = (uu___114_1455.beta);
            iota = (uu___114_1455.iota);
            zeta = (uu___114_1455.zeta);
            weak = (uu___114_1455.weak);
            hnf = (uu___114_1455.hnf);
            primops = (uu___114_1455.primops);
            do_not_unfold_pure_lets = (uu___114_1455.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1455.unfold_until);
            unfold_only = (uu___114_1455.unfold_only);
            unfold_fully = (uu___114_1455.unfold_fully);
            unfold_attr = (uu___114_1455.unfold_attr);
            unfold_tac = (uu___114_1455.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1455.pure_subterms_within_computations);
            simplify = (uu___114_1455.simplify);
            erase_universes = (uu___114_1455.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1455.reify_);
            compress_uvars = (uu___114_1455.compress_uvars);
            no_full_norm = (uu___114_1455.no_full_norm);
            check_no_uvars = (uu___114_1455.check_no_uvars);
            unmeta = (uu___114_1455.unmeta);
            unascribe = (uu___114_1455.unascribe);
            in_full_norm_request = (uu___114_1455.in_full_norm_request)
          }
      | Reify  ->
          let uu___115_1456 = fs  in
          {
            beta = (uu___115_1456.beta);
            iota = (uu___115_1456.iota);
            zeta = (uu___115_1456.zeta);
            weak = (uu___115_1456.weak);
            hnf = (uu___115_1456.hnf);
            primops = (uu___115_1456.primops);
            do_not_unfold_pure_lets = (uu___115_1456.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1456.unfold_until);
            unfold_only = (uu___115_1456.unfold_only);
            unfold_fully = (uu___115_1456.unfold_fully);
            unfold_attr = (uu___115_1456.unfold_attr);
            unfold_tac = (uu___115_1456.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1456.pure_subterms_within_computations);
            simplify = (uu___115_1456.simplify);
            erase_universes = (uu___115_1456.erase_universes);
            allow_unbound_universes = (uu___115_1456.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1456.compress_uvars);
            no_full_norm = (uu___115_1456.no_full_norm);
            check_no_uvars = (uu___115_1456.check_no_uvars);
            unmeta = (uu___115_1456.unmeta);
            unascribe = (uu___115_1456.unascribe);
            in_full_norm_request = (uu___115_1456.in_full_norm_request)
          }
      | CompressUvars  ->
          let uu___116_1457 = fs  in
          {
            beta = (uu___116_1457.beta);
            iota = (uu___116_1457.iota);
            zeta = (uu___116_1457.zeta);
            weak = (uu___116_1457.weak);
            hnf = (uu___116_1457.hnf);
            primops = (uu___116_1457.primops);
            do_not_unfold_pure_lets = (uu___116_1457.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1457.unfold_until);
            unfold_only = (uu___116_1457.unfold_only);
            unfold_fully = (uu___116_1457.unfold_fully);
            unfold_attr = (uu___116_1457.unfold_attr);
            unfold_tac = (uu___116_1457.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1457.pure_subterms_within_computations);
            simplify = (uu___116_1457.simplify);
            erase_universes = (uu___116_1457.erase_universes);
            allow_unbound_universes = (uu___116_1457.allow_unbound_universes);
            reify_ = (uu___116_1457.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1457.no_full_norm);
            check_no_uvars = (uu___116_1457.check_no_uvars);
            unmeta = (uu___116_1457.unmeta);
            unascribe = (uu___116_1457.unascribe);
            in_full_norm_request = (uu___116_1457.in_full_norm_request)
          }
      | NoFullNorm  ->
          let uu___117_1458 = fs  in
          {
            beta = (uu___117_1458.beta);
            iota = (uu___117_1458.iota);
            zeta = (uu___117_1458.zeta);
            weak = (uu___117_1458.weak);
            hnf = (uu___117_1458.hnf);
            primops = (uu___117_1458.primops);
            do_not_unfold_pure_lets = (uu___117_1458.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1458.unfold_until);
            unfold_only = (uu___117_1458.unfold_only);
            unfold_fully = (uu___117_1458.unfold_fully);
            unfold_attr = (uu___117_1458.unfold_attr);
            unfold_tac = (uu___117_1458.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1458.pure_subterms_within_computations);
            simplify = (uu___117_1458.simplify);
            erase_universes = (uu___117_1458.erase_universes);
            allow_unbound_universes = (uu___117_1458.allow_unbound_universes);
            reify_ = (uu___117_1458.reify_);
            compress_uvars = (uu___117_1458.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1458.check_no_uvars);
            unmeta = (uu___117_1458.unmeta);
            unascribe = (uu___117_1458.unascribe);
            in_full_norm_request = (uu___117_1458.in_full_norm_request)
          }
      | CheckNoUvars  ->
          let uu___118_1459 = fs  in
          {
            beta = (uu___118_1459.beta);
            iota = (uu___118_1459.iota);
            zeta = (uu___118_1459.zeta);
            weak = (uu___118_1459.weak);
            hnf = (uu___118_1459.hnf);
            primops = (uu___118_1459.primops);
            do_not_unfold_pure_lets = (uu___118_1459.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1459.unfold_until);
            unfold_only = (uu___118_1459.unfold_only);
            unfold_fully = (uu___118_1459.unfold_fully);
            unfold_attr = (uu___118_1459.unfold_attr);
            unfold_tac = (uu___118_1459.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1459.pure_subterms_within_computations);
            simplify = (uu___118_1459.simplify);
            erase_universes = (uu___118_1459.erase_universes);
            allow_unbound_universes = (uu___118_1459.allow_unbound_universes);
            reify_ = (uu___118_1459.reify_);
            compress_uvars = (uu___118_1459.compress_uvars);
            no_full_norm = (uu___118_1459.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1459.unmeta);
            unascribe = (uu___118_1459.unascribe);
            in_full_norm_request = (uu___118_1459.in_full_norm_request)
          }
      | Unmeta  ->
          let uu___119_1460 = fs  in
          {
            beta = (uu___119_1460.beta);
            iota = (uu___119_1460.iota);
            zeta = (uu___119_1460.zeta);
            weak = (uu___119_1460.weak);
            hnf = (uu___119_1460.hnf);
            primops = (uu___119_1460.primops);
            do_not_unfold_pure_lets = (uu___119_1460.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1460.unfold_until);
            unfold_only = (uu___119_1460.unfold_only);
            unfold_fully = (uu___119_1460.unfold_fully);
            unfold_attr = (uu___119_1460.unfold_attr);
            unfold_tac = (uu___119_1460.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1460.pure_subterms_within_computations);
            simplify = (uu___119_1460.simplify);
            erase_universes = (uu___119_1460.erase_universes);
            allow_unbound_universes = (uu___119_1460.allow_unbound_universes);
            reify_ = (uu___119_1460.reify_);
            compress_uvars = (uu___119_1460.compress_uvars);
            no_full_norm = (uu___119_1460.no_full_norm);
            check_no_uvars = (uu___119_1460.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1460.unascribe);
            in_full_norm_request = (uu___119_1460.in_full_norm_request)
          }
      | Unascribe  ->
          let uu___120_1461 = fs  in
          {
            beta = (uu___120_1461.beta);
            iota = (uu___120_1461.iota);
            zeta = (uu___120_1461.zeta);
            weak = (uu___120_1461.weak);
            hnf = (uu___120_1461.hnf);
            primops = (uu___120_1461.primops);
            do_not_unfold_pure_lets = (uu___120_1461.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1461.unfold_until);
            unfold_only = (uu___120_1461.unfold_only);
            unfold_fully = (uu___120_1461.unfold_fully);
            unfold_attr = (uu___120_1461.unfold_attr);
            unfold_tac = (uu___120_1461.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1461.pure_subterms_within_computations);
            simplify = (uu___120_1461.simplify);
            erase_universes = (uu___120_1461.erase_universes);
            allow_unbound_universes = (uu___120_1461.allow_unbound_universes);
            reify_ = (uu___120_1461.reify_);
            compress_uvars = (uu___120_1461.compress_uvars);
            no_full_norm = (uu___120_1461.no_full_norm);
            check_no_uvars = (uu___120_1461.check_no_uvars);
            unmeta = (uu___120_1461.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1461.in_full_norm_request)
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1511  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
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
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
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
        auto_reflect = __fname__auto_reflect;
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
    match projectee with | Clos _0 -> true | uu____1790 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1894 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1907 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
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
             let uu____2205 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2205 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2219 = FStar_Util.psmap_empty ()  in add_steps uu____2219 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2234 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2234
  
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
  | Match of (env,branches,cfg,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2382 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2420 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2458 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2531 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2581 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2639 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2683 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2723 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2761 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2779 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2806 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2806 with | (hd1,uu____2820) -> hd1
  
let mk :
  'Auu____2843 .
    'Auu____2843 ->
      FStar_Range.range -> 'Auu____2843 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2906 = FStar_ST.op_Bang r  in
          match uu____2906 with
          | FStar_Pervasives_Native.Some uu____2958 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3034 =
      FStar_List.map
        (fun uu____3048  ->
           match uu____3048 with
           | (bopt,c) ->
               let uu____3061 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3063 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3061 uu____3063) env
       in
    FStar_All.pipe_right uu____3034 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_3066  ->
    match uu___79_3066 with
    | Clos (env,t,uu____3069,uu____3070) ->
        let uu____3115 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3122 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3115 uu____3122
    | Univ uu____3123 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_3128  ->
    match uu___80_3128 with
    | Arg (c,uu____3130,uu____3131) ->
        let uu____3132 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3132
    | MemoLazy uu____3133 -> "MemoLazy"
    | Abs (uu____3140,bs,uu____3142,uu____3143,uu____3144) ->
        let uu____3149 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3149
    | UnivArgs uu____3154 -> "UnivArgs"
    | Match uu____3161 -> "Match"
    | App (uu____3170,t,uu____3172,uu____3173) ->
        let uu____3174 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3174
    | Meta (uu____3175,m,uu____3177) -> "Meta"
    | Let uu____3178 -> "Let"
    | Cfg uu____3187 -> "Cfg"
    | Debug (t,uu____3189) ->
        let uu____3190 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3190
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3200 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3200 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3241 . 'Auu____3241 Prims.list -> Prims.bool =
  fun uu___81_3248  ->
    match uu___81_3248 with | [] -> true | uu____3251 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3283 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3283
      with
      | uu____3302 ->
          let uu____3303 =
            let uu____3304 = FStar_Syntax_Print.db_to_string x  in
            let uu____3305 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3304
              uu____3305
             in
          failwith uu____3303
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3313 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3313
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3317 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3317
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3321 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3321
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____3355 =
            FStar_List.fold_left
              (fun uu____3381  ->
                 fun u1  ->
                   match uu____3381 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3406 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3406 with
                        | (k_u,n1) ->
                            let uu____3421 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3421
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3355 with
          | (uu____3439,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3466 =
                   let uu____3467 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3467  in
                 match uu____3466 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3485 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3493 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3499 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3508 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3517 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3524 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3524 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3541 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3541 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3549 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3557 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3557 with
                                  | (uu____3562,m) -> n1 <= m))
                           in
                        if uu____3549 then rest1 else us1
                    | uu____3567 -> us1)
               | uu____3572 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3576 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3576
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3580 = aux u  in
           match uu____3580 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (inline_closure_env :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let uu____3721 =
            log cfg
              (fun uu____3726  ->
                 let uu____3727 = FStar_Syntax_Print.tag_of_term t  in
                 let uu____3728 = env_to_string env  in
                 let uu____3729 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                   uu____3727 uu____3728 uu____3729)
             in
          match env with
          | [] when
              FStar_All.pipe_left Prims.op_Negation
                (cfg.steps).compress_uvars
              -> rebuild_closure cfg env stack t
          | uu____3738 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____3741 ->
                   let uu____3766 = FStar_Syntax_Subst.compress t  in
                   inline_closure_env cfg env stack uu____3766
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_constant uu____3767 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_name uu____3768 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_lazy uu____3769 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_fvar uu____3770 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_uvar uu____3771 ->
                   if (cfg.steps).check_no_uvars
                   then
                     let t1 = FStar_Syntax_Subst.compress t  in
                     (match t1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_uvar uu____3793 ->
                          let uu____3810 =
                            let uu____3811 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____3812 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.format2
                              "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                              uu____3811 uu____3812
                             in
                          failwith uu____3810
                      | uu____3815 -> inline_closure_env cfg env stack t1)
                   else rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_type u ->
                   let t1 =
                     let uu____3821 =
                       let uu____3822 = norm_universe cfg env u  in
                       FStar_Syntax_Syntax.Tm_type uu____3822  in
                     mk uu____3821 t.FStar_Syntax_Syntax.pos  in
                   rebuild_closure cfg env stack t1
               | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                   let t1 =
                     let uu____3830 =
                       FStar_List.map (norm_universe cfg env) us  in
                     FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3830  in
                   rebuild_closure cfg env stack t1
               | FStar_Syntax_Syntax.Tm_bvar x ->
                   let uu____3832 = lookup_bvar env x  in
                   (match uu____3832 with
                    | Univ uu____3835 ->
                        failwith
                          "Impossible: term variable is bound to a universe"
                    | Dummy  ->
                        let x1 =
                          let uu___125_3839 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___125_3839.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___125_3839.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              FStar_Syntax_Syntax.tun
                          }  in
                        let t1 =
                          mk (FStar_Syntax_Syntax.Tm_bvar x1)
                            t.FStar_Syntax_Syntax.pos
                           in
                        rebuild_closure cfg env stack t1
                    | Clos (env1,t0,uu____3845,uu____3846) ->
                        inline_closure_env cfg env1 stack t0)
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let stack1 =
                     FStar_All.pipe_right stack
                       (FStar_List.fold_right
                          (fun uu____3931  ->
                             fun stack1  ->
                               match uu____3931 with
                               | (a,aq) ->
                                   let uu____3943 =
                                     let uu____3944 =
                                       let uu____3951 =
                                         let uu____3952 =
                                           let uu____3983 =
                                             FStar_Util.mk_ref
                                               FStar_Pervasives_Native.None
                                              in
                                           (env, a, uu____3983, false)  in
                                         Clos uu____3952  in
                                       (uu____3951, aq,
                                         (t.FStar_Syntax_Syntax.pos))
                                        in
                                     Arg uu____3944  in
                                   uu____3943 :: stack1) args)
                      in
                   inline_closure_env cfg env stack1 head1
               | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                   let env' =
                     FStar_All.pipe_right env
                       (FStar_List.fold_right
                          (fun _b  ->
                             fun env1  ->
                               (FStar_Pervasives_Native.None, Dummy) :: env1)
                          bs)
                      in
                   let stack1 =
                     (Abs (env, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                     :: stack  in
                   inline_closure_env cfg env' stack1 body
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                   let uu____4177 = close_binders cfg env bs  in
                   (match uu____4177 with
                    | (bs1,env') ->
                        let c1 = close_comp cfg env' c  in
                        let t1 =
                          mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                            t.FStar_Syntax_Syntax.pos
                           in
                        rebuild_closure cfg env stack t1)
               | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                   let uu____4224 =
                     let uu____4235 =
                       let uu____4242 = FStar_Syntax_Syntax.mk_binder x  in
                       [uu____4242]  in
                     close_binders cfg env uu____4235  in
                   (match uu____4224 with
                    | (x1,env1) ->
                        let phi1 = non_tail_inline_closure_env cfg env1 phi
                           in
                        let t1 =
                          let uu____4265 =
                            let uu____4266 =
                              let uu____4273 =
                                let uu____4274 = FStar_List.hd x1  in
                                FStar_All.pipe_right uu____4274
                                  FStar_Pervasives_Native.fst
                                 in
                              (uu____4273, phi1)  in
                            FStar_Syntax_Syntax.Tm_refine uu____4266  in
                          mk uu____4265 t.FStar_Syntax_Syntax.pos  in
                        rebuild_closure cfg env1 stack t1)
               | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                   let annot1 =
                     match annot with
                     | FStar_Util.Inl t2 ->
                         let uu____4365 =
                           non_tail_inline_closure_env cfg env t2  in
                         FStar_Util.Inl uu____4365
                     | FStar_Util.Inr c ->
                         let uu____4379 = close_comp cfg env c  in
                         FStar_Util.Inr uu____4379
                      in
                   let tacopt1 =
                     FStar_Util.map_opt tacopt
                       (non_tail_inline_closure_env cfg env)
                      in
                   let t2 =
                     let uu____4398 =
                       let uu____4399 =
                         let uu____4426 =
                           non_tail_inline_closure_env cfg env t1  in
                         (uu____4426, (annot1, tacopt1), lopt)  in
                       FStar_Syntax_Syntax.Tm_ascribed uu____4399  in
                     mk uu____4398 t.FStar_Syntax_Syntax.pos  in
                   rebuild_closure cfg env stack t2
               | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                   let t1 =
                     match qi.FStar_Syntax_Syntax.qkind with
                     | FStar_Syntax_Syntax.Quote_dynamic  ->
                         let uu____4472 =
                           let uu____4473 =
                             let uu____4480 =
                               non_tail_inline_closure_env cfg env t'  in
                             (uu____4480, qi)  in
                           FStar_Syntax_Syntax.Tm_quoted uu____4473  in
                         mk uu____4472 t.FStar_Syntax_Syntax.pos
                     | FStar_Syntax_Syntax.Quote_static  ->
                         let qi1 =
                           FStar_Syntax_Syntax.on_antiquoted
                             (non_tail_inline_closure_env cfg env) qi
                            in
                         mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                           t.FStar_Syntax_Syntax.pos
                      in
                   rebuild_closure cfg env stack t1
               | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                   let stack1 = (Meta (env, m, (t.FStar_Syntax_Syntax.pos)))
                     :: stack  in
                   inline_closure_env cfg env stack1 t'
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let env0 = env  in
                   let env1 =
                     FStar_List.fold_left
                       (fun env1  -> fun uu____4532  -> dummy :: env1) env
                       lb.FStar_Syntax_Syntax.lbunivs
                      in
                   let typ =
                     non_tail_inline_closure_env cfg env1
                       lb.FStar_Syntax_Syntax.lbtyp
                      in
                   let def =
                     non_tail_inline_closure_env cfg env1
                       lb.FStar_Syntax_Syntax.lbdef
                      in
                   let uu____4553 =
                     let uu____4564 = FStar_Syntax_Syntax.is_top_level [lb]
                        in
                     if uu____4564
                     then ((lb.FStar_Syntax_Syntax.lbname), body)
                     else
                       (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                           in
                        let uu____4583 =
                          non_tail_inline_closure_env cfg (dummy :: env0)
                            body
                           in
                        ((FStar_Util.Inl
                            (let uu___126_4599 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___126_4599.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___126_4599.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = typ
                             })), uu____4583))
                      in
                   (match uu____4553 with
                    | (nm,body1) ->
                        let lb1 =
                          let uu___127_4617 = lb  in
                          {
                            FStar_Syntax_Syntax.lbname = nm;
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___127_4617.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp = typ;
                            FStar_Syntax_Syntax.lbeff =
                              (uu___127_4617.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef = def;
                            FStar_Syntax_Syntax.lbattrs =
                              (uu___127_4617.FStar_Syntax_Syntax.lbattrs);
                            FStar_Syntax_Syntax.lbpos =
                              (uu___127_4617.FStar_Syntax_Syntax.lbpos)
                          }  in
                        let t1 =
                          mk
                            (FStar_Syntax_Syntax.Tm_let
                               ((false, [lb1]), body1))
                            t.FStar_Syntax_Syntax.pos
                           in
                        rebuild_closure cfg env0 stack t1)
               | FStar_Syntax_Syntax.Tm_let ((uu____4631,lbs),body) ->
                   let norm_one_lb env1 lb =
                     let env_univs =
                       FStar_List.fold_right
                         (fun uu____4694  -> fun env2  -> dummy :: env2)
                         lb.FStar_Syntax_Syntax.lbunivs env1
                        in
                     let env2 =
                       let uu____4719 = FStar_Syntax_Syntax.is_top_level lbs
                          in
                       if uu____4719
                       then env_univs
                       else
                         FStar_List.fold_right
                           (fun uu____4739  -> fun env2  -> dummy :: env2)
                           lbs env_univs
                        in
                     let ty =
                       non_tail_inline_closure_env cfg env_univs
                         lb.FStar_Syntax_Syntax.lbtyp
                        in
                     let nm =
                       let uu____4763 = FStar_Syntax_Syntax.is_top_level lbs
                          in
                       if uu____4763
                       then lb.FStar_Syntax_Syntax.lbname
                       else
                         (let x =
                            FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                          FStar_Util.Inl
                            (let uu___128_4771 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___128_4771.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___128_4771.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }))
                        in
                     let uu___129_4772 = lb  in
                     let uu____4773 =
                       non_tail_inline_closure_env cfg env2
                         lb.FStar_Syntax_Syntax.lbdef
                        in
                     {
                       FStar_Syntax_Syntax.lbname = nm;
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___129_4772.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp = ty;
                       FStar_Syntax_Syntax.lbeff =
                         (uu___129_4772.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef = uu____4773;
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___129_4772.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___129_4772.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let lbs1 =
                     FStar_All.pipe_right lbs
                       (FStar_List.map (norm_one_lb env))
                      in
                   let body1 =
                     let body_env =
                       FStar_List.fold_right
                         (fun uu____4805  -> fun env1  -> dummy :: env1) lbs1
                         env
                        in
                     non_tail_inline_closure_env cfg body_env body  in
                   let t1 =
                     mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                       t.FStar_Syntax_Syntax.pos
                      in
                   rebuild_closure cfg env stack t1
               | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                   let stack1 =
                     (Match (env, branches, cfg, (t.FStar_Syntax_Syntax.pos)))
                     :: stack  in
                   inline_closure_env cfg env stack1 head1)

and (non_tail_inline_closure_env :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg  -> fun env  -> fun t  -> inline_closure_env cfg env [] t

and (rebuild_closure :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let uu____4902 =
            log cfg
              (fun uu____4908  ->
                 let uu____4909 = FStar_Syntax_Print.tag_of_term t  in
                 let uu____4910 = env_to_string env  in
                 let uu____4911 = stack_to_string stack  in
                 let uu____4912 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.print4
                   "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                   uu____4909 uu____4910 uu____4911 uu____4912)
             in
          match stack with
          | [] -> t
          | (Arg (Clos (env_arg,tm,uu____4917,uu____4918),aq,r))::stack1 ->
              let stack2 = (App (env, t, aq, r)) :: stack1  in
              inline_closure_env cfg env_arg stack2 tm
          | (App (env1,head1,aq,r))::stack1 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r
                 in
              rebuild_closure cfg env1 stack1 t1
          | (Abs (env',bs,env'',lopt,r))::stack1 ->
              let uu____4993 = close_binders cfg env' bs  in
              (match uu____4993 with
               | (bs1,uu____5007) ->
                   let lopt1 = close_lcomp_opt cfg env'' lopt  in
                   let uu____5023 =
                     let uu___130_5024 = FStar_Syntax_Util.abs bs1 t lopt1
                        in
                     {
                       FStar_Syntax_Syntax.n =
                         (uu___130_5024.FStar_Syntax_Syntax.n);
                       FStar_Syntax_Syntax.pos = r;
                       FStar_Syntax_Syntax.vars =
                         (uu___130_5024.FStar_Syntax_Syntax.vars)
                     }  in
                   rebuild_closure cfg env stack1 uu____5023)
          | (Match (env1,branches,cfg1,r))::stack1 ->
              let close_one_branch env2 uu____5070 =
                match uu____5070 with
                | (pat,w_opt,tm) ->
                    let rec norm_pat env3 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____5145 ->
                          (p, env3)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____5166 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____5226  ->
                                    fun uu____5227  ->
                                      match (uu____5226, uu____5227) with
                                      | ((pats1,env4),(p1,b)) ->
                                          let uu____5318 = norm_pat env4 p1
                                             in
                                          (match uu____5318 with
                                           | (p2,env5) ->
                                               (((p2, b) :: pats1), env5)))
                                 ([], env3))
                             in
                          (match uu____5166 with
                           | (pats1,env4) ->
                               ((let uu___131_5400 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___131_5400.FStar_Syntax_Syntax.p)
                                 }), env4))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___132_5419 = x  in
                            let uu____5420 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___132_5419.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___132_5419.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5420
                            }  in
                          ((let uu___133_5434 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___133_5434.FStar_Syntax_Syntax.p)
                            }), (dummy :: env3))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___134_5445 = x  in
                            let uu____5446 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___134_5445.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___134_5445.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5446
                            }  in
                          ((let uu___135_5460 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___135_5460.FStar_Syntax_Syntax.p)
                            }), (dummy :: env3))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___136_5476 = x  in
                            let uu____5477 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___136_5476.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___136_5476.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5477
                            }  in
                          let t2 = non_tail_inline_closure_env cfg1 env3 t1
                             in
                          ((let uu___137_5486 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___137_5486.FStar_Syntax_Syntax.p)
                            }), env3)
                       in
                    let uu____5491 = norm_pat env2 pat  in
                    (match uu____5491 with
                     | (pat1,env3) ->
                         let w_opt1 =
                           match w_opt with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some w ->
                               let uu____5536 =
                                 non_tail_inline_closure_env cfg1 env3 w  in
                               FStar_Pervasives_Native.Some uu____5536
                            in
                         let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                            in
                         (pat1, w_opt1, tm1))
                 in
              let t1 =
                let uu____5555 =
                  let uu____5556 =
                    let uu____5579 =
                      FStar_All.pipe_right branches
                        (FStar_List.map (close_one_branch env1))
                       in
                    (t, uu____5579)  in
                  FStar_Syntax_Syntax.Tm_match uu____5556  in
                mk uu____5555 t.FStar_Syntax_Syntax.pos  in
              rebuild_closure cfg1 env1 stack1 t1
          | (Meta (env_m,m,r))::stack1 ->
              let m1 =
                match m with
                | FStar_Syntax_Syntax.Meta_pattern args ->
                    let uu____5674 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun args1  ->
                              FStar_All.pipe_right args1
                                (FStar_List.map
                                   (fun uu____5763  ->
                                      match uu____5763 with
                                      | (a,q) ->
                                          let uu____5782 =
                                            non_tail_inline_closure_env cfg
                                              env_m a
                                             in
                                          (uu____5782, q)))))
                       in
                    FStar_Syntax_Syntax.Meta_pattern uu____5674
                | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                    let uu____5793 =
                      let uu____5800 =
                        non_tail_inline_closure_env cfg env_m tbody  in
                      (m1, uu____5800)  in
                    FStar_Syntax_Syntax.Meta_monadic uu____5793
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                    let uu____5812 =
                      let uu____5821 =
                        non_tail_inline_closure_env cfg env_m tbody  in
                      (m1, m2, uu____5821)  in
                    FStar_Syntax_Syntax.Meta_monadic_lift uu____5812
                | uu____5826 -> m  in
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
              rebuild_closure cfg env stack1 t1
          | uu____5830 -> failwith "Impossible: unexpected stack element"

and (close_binders :
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
        let uu____5844 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5893  ->
                  fun uu____5894  ->
                    match (uu____5893, uu____5894) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_5964 = b  in
                          let uu____5965 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_5964.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_5964.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5965
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5844 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6058 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6071 = inline_closure_env cfg env [] t  in
                 let uu____6072 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6071 uu____6072
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6085 = inline_closure_env cfg env [] t  in
                 let uu____6086 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6085 uu____6086
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6132  ->
                           match uu____6132 with
                           | (a,q) ->
                               let uu____6145 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6145, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_6160  ->
                           match uu___82_6160 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6164 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6164
                           | f -> f))
                    in
                 let uu____6168 =
                   let uu___139_6169 = c1  in
                   let uu____6170 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6170;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_6169.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6168)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_6180  ->
            match uu___83_6180 with
            | FStar_Syntax_Syntax.DECREASES uu____6181 -> false
            | uu____6184 -> true))

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
                   (fun uu___84_6202  ->
                      match uu___84_6202 with
                      | FStar_Syntax_Syntax.DECREASES uu____6203 -> false
                      | uu____6206 -> true))
               in
            let rc1 =
              let uu___140_6208 = rc  in
              let uu____6209 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_6208.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6209;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6218 -> lopt

let (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list e a =
    let uu____6331 =
      let uu____6340 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6340  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6331  in
  let arg_as_bounded_int uu____6366 =
    match uu____6366 with
    | (a,uu____6378) ->
        let uu____6385 =
          let uu____6386 = FStar_Syntax_Subst.compress a  in
          uu____6386.FStar_Syntax_Syntax.n  in
        (match uu____6385 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6396;
                FStar_Syntax_Syntax.vars = uu____6397;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6399;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6400;_},uu____6401)::[])
             when
             let uu____6440 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6440 "int_to_t" ->
             let uu____6441 =
               let uu____6446 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6446)  in
             FStar_Pervasives_Native.Some uu____6441
         | uu____6451 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6499 = f a  in FStar_Pervasives_Native.Some uu____6499
    | uu____6500 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6556 = f a0 a1  in FStar_Pervasives_Native.Some uu____6556
    | uu____6557 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6615 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6615  in
  let binary_op as_a f res args =
    let uu____6680 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6680  in
  let as_primitive_step is_strong uu____6711 =
    match uu____6711 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____6771 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6771)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6807 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6807)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____6836 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____6836)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6872 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____6872)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6908 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____6908)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7040 =
          let uu____7049 = as_a a  in
          let uu____7052 = as_b b  in (uu____7049, uu____7052)  in
        (match uu____7040 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7067 =
               let uu____7068 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7068  in
             FStar_Pervasives_Native.Some uu____7067
         | uu____7069 -> FStar_Pervasives_Native.None)
    | uu____7078 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7098 =
        let uu____7099 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7099  in
      mk uu____7098 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7111 =
      let uu____7114 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7114  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7111  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7156 =
      let uu____7157 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7157  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7156
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7179 = arg_as_string a1  in
        (match uu____7179 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7185 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7185 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7198 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7198
              | uu____7199 -> FStar_Pervasives_Native.None)
         | uu____7204 -> FStar_Pervasives_Native.None)
    | uu____7207 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7221 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7221
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7258 =
          let uu____7279 = arg_as_string fn  in
          let uu____7282 = arg_as_int from_line  in
          let uu____7285 = arg_as_int from_col  in
          let uu____7288 = arg_as_int to_line  in
          let uu____7291 = arg_as_int to_col  in
          (uu____7279, uu____7282, uu____7285, uu____7288, uu____7291)  in
        (match uu____7258 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7322 =
                 let uu____7323 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7324 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7323 uu____7324  in
               let uu____7325 =
                 let uu____7326 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7327 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7326 uu____7327  in
               FStar_Range.mk_range fn1 uu____7322 uu____7325  in
             let uu____7328 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7328
         | uu____7329 -> FStar_Pervasives_Native.None)
    | uu____7350 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7383)::(a1,uu____7385)::(a2,uu____7387)::[] ->
        let uu____7424 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7424 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7437 -> FStar_Pervasives_Native.None)
    | uu____7438 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7469)::[] ->
        let uu____7478 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7478 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7484 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7484
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7485 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7511 =
      let uu____7528 =
        let uu____7545 =
          let uu____7562 =
            let uu____7579 =
              let uu____7596 =
                let uu____7613 =
                  let uu____7630 =
                    let uu____7647 =
                      let uu____7664 =
                        let uu____7681 =
                          let uu____7698 =
                            let uu____7715 =
                              let uu____7732 =
                                let uu____7749 =
                                  let uu____7766 =
                                    let uu____7783 =
                                      let uu____7800 =
                                        let uu____7817 =
                                          let uu____7834 =
                                            let uu____7851 =
                                              let uu____7868 =
                                                let uu____7883 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7883,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____7892 =
                                                let uu____7909 =
                                                  let uu____7924 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7924,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____7937 =
                                                  let uu____7954 =
                                                    let uu____7971 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7971,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7982 =
                                                    let uu____8001 =
                                                      let uu____8018 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8018,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8001]  in
                                                  uu____7954 :: uu____7982
                                                   in
                                                uu____7909 :: uu____7937  in
                                              uu____7868 :: uu____7892  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7851
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7834
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7817
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7800
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7783
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8246 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8246 y)))
                                    :: uu____7766
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7749
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7732
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7715
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7698
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7681
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7664
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8441 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8441)))
                      :: uu____7647
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8471 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8471)))
                    :: uu____7630
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8501 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8501)))
                  :: uu____7613
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8531 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8531)))
                :: uu____7596
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7579
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7562
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7545
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7528
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7511
     in
  let weak_ops =
    let uu____8692 =
      let uu____8713 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8713, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8692]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8811 =
        let uu____8816 =
          let uu____8817 = FStar_Syntax_Syntax.as_arg c  in [uu____8817]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8816  in
      uu____8811 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8873 =
                let uu____8888 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____8888, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____8910  ->
                          fun uu____8911  ->
                            match (uu____8910, uu____8911) with
                            | ((int_to_t1,x),(uu____8930,y)) ->
                                let uu____8940 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____8940)))
                 in
              let uu____8941 =
                let uu____8958 =
                  let uu____8973 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____8973, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____8995  ->
                            fun uu____8996  ->
                              match (uu____8995, uu____8996) with
                              | ((int_to_t1,x),(uu____9015,y)) ->
                                  let uu____9025 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9025)))
                   in
                let uu____9026 =
                  let uu____9043 =
                    let uu____9058 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9058, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9080  ->
                              fun uu____9081  ->
                                match (uu____9080, uu____9081) with
                                | ((int_to_t1,x),(uu____9100,y)) ->
                                    let uu____9110 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9110)))
                     in
                  let uu____9111 =
                    let uu____9128 =
                      let uu____9143 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9143, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9161  ->
                                match uu____9161 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9128]  in
                  uu____9043 :: uu____9111  in
                uu____8958 :: uu____9026  in
              uu____8873 :: uu____8941))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9291 =
                let uu____9306 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9306, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9328  ->
                          fun uu____9329  ->
                            match (uu____9328, uu____9329) with
                            | ((int_to_t1,x),(uu____9348,y)) ->
                                let uu____9358 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9358)))
                 in
              let uu____9359 =
                let uu____9376 =
                  let uu____9391 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9391, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9413  ->
                            fun uu____9414  ->
                              match (uu____9413, uu____9414) with
                              | ((int_to_t1,x),(uu____9433,y)) ->
                                  let uu____9443 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9443)))
                   in
                [uu____9376]  in
              uu____9291 :: uu____9359))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____9573)::(a1,uu____9575)::(a2,uu____9577)::[] ->
        let uu____9614 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9614 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9620 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9620.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9620.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9624 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9624.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9624.FStar_Syntax_Syntax.vars)
                })
         | uu____9625 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9627)::uu____9628::(a1,uu____9630)::(a2,uu____9632)::[] ->
        let uu____9681 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9681 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9687 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9687.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9687.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9691 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9691.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9691.FStar_Syntax_Syntax.vars)
                })
         | uu____9692 -> FStar_Pervasives_Native.None)
    | uu____9693 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9747 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9747 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        let uu____9792 =
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
            (FStar_Errors.Warning_UnembedBinderKnot,
              "unembed_binder_knot is unset!")
           in
        FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____9799 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9799) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9861  ->
           fun subst1  ->
             match uu____9861 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9902,uu____9903)) ->
                      let uu____9962 = b  in
                      (match uu____9962 with
                       | (bv,uu____9970) ->
                           let uu____9971 =
                             let uu____9972 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____9972  in
                           if uu____9971
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____9977 = unembed_binder term1  in
                              match uu____9977 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____9984 =
                                      let uu___143_9985 = bv  in
                                      let uu____9986 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_9985.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_9985.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____9986
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____9984
                                     in
                                  let b_for_x =
                                    let uu____9990 =
                                      let uu____9997 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____9997)
                                       in
                                    FStar_Syntax_Syntax.NT uu____9990  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_10007  ->
                                         match uu___85_10007 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10008,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10010;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10011;_})
                                             ->
                                             let uu____10016 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10016
                                         | uu____10017 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10018 -> subst1)) env []
  
let reduce_primops :
  'Auu____10041 'Auu____10042 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10041) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10042 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10088 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10088 with
             | (head1,args) ->
                 let uu____10125 =
                   let uu____10126 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10126.FStar_Syntax_Syntax.n  in
                 (match uu____10125 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10130 = find_prim_step cfg fv  in
                      (match uu____10130 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             let uu____10147 =
                               log_primops cfg
                                 (fun uu____10152  ->
                                    let uu____10153 =
                                      FStar_Syntax_Print.lid_to_string
                                        prim_step.name
                                       in
                                    let uu____10154 =
                                      FStar_Util.string_of_int l  in
                                    let uu____10161 =
                                      FStar_Util.string_of_int
                                        prim_step.arity
                                       in
                                    FStar_Util.print3
                                      "primop: found partially applied %s (%s/%s args)\n"
                                      uu____10153 uu____10154 uu____10161)
                                in
                             tm
                           else
                             (let uu____10163 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10163 with
                              | (args_1,args_2) ->
                                  let uu____10271 =
                                    log_primops cfg
                                      (fun uu____10274  ->
                                         let uu____10275 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: trying to reduce <%s>\n"
                                           uu____10275)
                                     in
                                  let psc =
                                    {
                                      psc_range =
                                        (head1.FStar_Syntax_Syntax.pos);
                                      psc_subst =
                                        (fun uu____10278  ->
                                           if
                                             prim_step.requires_binder_substitution
                                           then mk_psc_subst cfg env
                                           else [])
                                    }  in
                                  let uu____10280 =
                                    prim_step.interpretation psc args_1  in
                                  (match uu____10280 with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____10283 =
                                         log_primops cfg
                                           (fun uu____10286  ->
                                              let uu____10287 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10287)
                                          in
                                       tm
                                   | FStar_Pervasives_Native.Some reduced ->
                                       let uu____10289 =
                                         log_primops cfg
                                           (fun uu____10293  ->
                                              let uu____10294 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10295 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10294 uu____10295)
                                          in
                                       FStar_Syntax_Util.mk_app reduced
                                         args_2))
                       | FStar_Pervasives_Native.Some uu____10296 ->
                           let uu____10297 =
                             log_primops cfg
                               (fun uu____10300  ->
                                  let uu____10301 =
                                    FStar_Syntax_Print.term_to_string tm  in
                                  FStar_Util.print1
                                    "primop: not reducing <%s> since we're doing strong reduction\n"
                                    uu____10301)
                              in
                           tm
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      let uu____10302 =
                        log_primops cfg
                          (fun uu____10305  ->
                             let uu____10306 =
                               FStar_Syntax_Print.term_to_string tm  in
                             FStar_Util.print1 "primop: reducing <%s>\n"
                               uu____10306)
                         in
                      (match args with
                       | (a1,uu____10308)::[] ->
                           FStar_Syntax_Embeddings.embed
                             FStar_Syntax_Embeddings.e_range
                             tm.FStar_Syntax_Syntax.pos
                             a1.FStar_Syntax_Syntax.pos
                       | uu____10325 -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      let uu____10334 =
                        log_primops cfg
                          (fun uu____10337  ->
                             let uu____10338 =
                               FStar_Syntax_Print.term_to_string tm  in
                             FStar_Util.print1 "primop: reducing <%s>\n"
                               uu____10338)
                         in
                      (match args with
                       | (t,uu____10340)::(r,uu____10342)::[] ->
                           let uu____10369 =
                             FStar_Syntax_Embeddings.unembed
                               FStar_Syntax_Embeddings.e_range r
                              in
                           (match uu____10369 with
                            | FStar_Pervasives_Native.Some rng ->
                                let uu___144_10373 = t  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___144_10373.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___144_10373.FStar_Syntax_Syntax.vars)
                                }
                            | FStar_Pervasives_Native.None  -> tm)
                       | uu____10376 -> tm)
                  | uu____10385 -> tm))
  
let reduce_equality :
  'Auu____10396 'Auu____10397 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10396) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10397 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_10441 = cfg  in
         {
           steps =
             (let uu___146_10444 = default_steps  in
              {
                beta = (uu___146_10444.beta);
                iota = (uu___146_10444.iota);
                zeta = (uu___146_10444.zeta);
                weak = (uu___146_10444.weak);
                hnf = (uu___146_10444.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_10444.do_not_unfold_pure_lets);
                unfold_until = (uu___146_10444.unfold_until);
                unfold_only = (uu___146_10444.unfold_only);
                unfold_fully = (uu___146_10444.unfold_fully);
                unfold_attr = (uu___146_10444.unfold_attr);
                unfold_tac = (uu___146_10444.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_10444.pure_subterms_within_computations);
                simplify = (uu___146_10444.simplify);
                erase_universes = (uu___146_10444.erase_universes);
                allow_unbound_universes =
                  (uu___146_10444.allow_unbound_universes);
                reify_ = (uu___146_10444.reify_);
                compress_uvars = (uu___146_10444.compress_uvars);
                no_full_norm = (uu___146_10444.no_full_norm);
                check_no_uvars = (uu___146_10444.check_no_uvars);
                unmeta = (uu___146_10444.unmeta);
                unascribe = (uu___146_10444.unascribe);
                in_full_norm_request = (uu___146_10444.in_full_norm_request)
              });
           tcenv = (uu___145_10441.tcenv);
           debug = (uu___145_10441.debug);
           delta_level = (uu___145_10441.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_10441.strong);
           memoize_lazy = (uu___145_10441.memoize_lazy);
           normalize_pure_lets = (uu___145_10441.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10451 .
    FStar_Syntax_Syntax.term -> 'Auu____10451 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10466 =
        let uu____10473 =
          let uu____10474 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10474.FStar_Syntax_Syntax.n  in
        (uu____10473, args)  in
      match uu____10466 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10480::uu____10481::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10485::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10490::uu____10491::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10494 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_10507  ->
    match uu___86_10507 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10513 =
          let uu____10516 =
            let uu____10517 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10517  in
          [uu____10516]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10513
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10523 =
          let uu____10526 =
            let uu____10527 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10527  in
          [uu____10526]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10523
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10548 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10548) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10594 =
          let uu____10599 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10599 s  in
        match uu____10594 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10615 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10615
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10632::(tm,uu____10634)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10663)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10684)::uu____10685::(tm,uu____10687)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10728 =
            let uu____10733 = full_norm steps  in parse_steps uu____10733  in
          (match uu____10728 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10772 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_10791  ->
    match uu___87_10791 with
    | (App
        (uu____10794,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10795;
                       FStar_Syntax_Syntax.vars = uu____10796;_},uu____10797,uu____10798))::uu____10799
        -> true
    | uu____10806 -> false
  
let firstn :
  'Auu____10815 .
    Prims.int ->
      'Auu____10815 Prims.list ->
        ('Auu____10815 Prims.list,'Auu____10815 Prims.list)
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
          (uu____10857,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10858;
                         FStar_Syntax_Syntax.vars = uu____10859;_},uu____10860,uu____10861))::uu____10862
          -> (cfg.steps).reify_
      | uu____10869 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10892) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10902) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____10921  ->
                  match uu____10921 with
                  | (a,uu____10929) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10935 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____10960 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____10961 -> false
    | FStar_Syntax_Syntax.Tm_type uu____10978 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____10979 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____10980 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____10981 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____10982 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____10983 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____10990 -> false
    | FStar_Syntax_Syntax.Tm_let uu____10997 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11010 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11027 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11040 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11086  ->
                   match uu____11086 with
                   | (a,uu____11094) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right pats
             (FStar_Util.for_some
                (fun uu____11171  ->
                   match uu____11171 with
                   | (uu____11186,wopt,t2) ->
                       (match wopt with
                        | FStar_Pervasives_Native.None  -> false
                        | FStar_Pervasives_Native.Some t3 ->
                            maybe_weakly_reduced t3)
                         || (maybe_weakly_reduced t2))))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11214) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Util.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern args ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____11336  ->
                        match uu____11336 with
                        | (a,uu____11344) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11349,uu____11350,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11356,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11362 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11369 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11370 -> false))
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            let uu____11661 =
              if (cfg.debug).norm_delayed
              then
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____11662 ->
                    let uu____11687 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "NORM delayed: %s\n" uu____11687
                | uu____11688 -> ()
              else ()  in
            FStar_Syntax_Subst.compress t  in
          let uu____11690 =
            log cfg
              (fun uu____11696  ->
                 let uu____11697 = FStar_Syntax_Print.tag_of_term t1  in
                 let uu____11698 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____11699 =
                   FStar_Util.string_of_int (FStar_List.length env)  in
                 let uu____11706 =
                   let uu____11707 =
                     let uu____11710 = firstn (Prims.parse_int "4") stack  in
                     FStar_All.pipe_left FStar_Pervasives_Native.fst
                       uu____11710
                      in
                   stack_to_string uu____11707  in
                 FStar_Util.print4
                   ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                   uu____11697 uu____11698 uu____11699 uu____11706)
             in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_constant uu____11733 ->
              rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_name uu____11734 ->
              rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_lazy uu____11735 ->
              rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_fvar
              { FStar_Syntax_Syntax.fv_name = uu____11736;
                FStar_Syntax_Syntax.fv_delta =
                  FStar_Syntax_Syntax.Delta_constant ;
                FStar_Syntax_Syntax.fv_qual = uu____11737;_}
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_fvar
              { FStar_Syntax_Syntax.fv_name = uu____11740;
                FStar_Syntax_Syntax.fv_delta = uu____11741;
                FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Data_ctor );_}
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_fvar
              { FStar_Syntax_Syntax.fv_name = uu____11742;
                FStar_Syntax_Syntax.fv_delta = uu____11743;
                FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Record_ctor uu____11744);_}
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_quoted uu____11751 ->
              let uu____11758 = closure_as_term cfg env t1  in
              rebuild cfg env stack uu____11758
          | FStar_Syntax_Syntax.Tm_app (hd1,args) when
              ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                 (is_norm_request hd1 args))
                &&
                (let uu____11788 =
                   FStar_Ident.lid_equals
                     (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                     FStar_Parser_Const.prims_lid
                    in
                 Prims.op_Negation uu____11788)
              ->
              let cfg' =
                let uu___147_11790 = cfg  in
                {
                  steps =
                    (let uu___148_11793 = cfg.steps  in
                     {
                       beta = (uu___148_11793.beta);
                       iota = (uu___148_11793.iota);
                       zeta = (uu___148_11793.zeta);
                       weak = (uu___148_11793.weak);
                       hnf = (uu___148_11793.hnf);
                       primops = (uu___148_11793.primops);
                       do_not_unfold_pure_lets = false;
                       unfold_until = (uu___148_11793.unfold_until);
                       unfold_only = FStar_Pervasives_Native.None;
                       unfold_fully = FStar_Pervasives_Native.None;
                       unfold_attr = (uu___148_11793.unfold_attr);
                       unfold_tac = (uu___148_11793.unfold_tac);
                       pure_subterms_within_computations =
                         (uu___148_11793.pure_subterms_within_computations);
                       simplify = (uu___148_11793.simplify);
                       erase_universes = (uu___148_11793.erase_universes);
                       allow_unbound_universes =
                         (uu___148_11793.allow_unbound_universes);
                       reify_ = (uu___148_11793.reify_);
                       compress_uvars = (uu___148_11793.compress_uvars);
                       no_full_norm = (uu___148_11793.no_full_norm);
                       check_no_uvars = (uu___148_11793.check_no_uvars);
                       unmeta = (uu___148_11793.unmeta);
                       unascribe = (uu___148_11793.unascribe);
                       in_full_norm_request =
                         (uu___148_11793.in_full_norm_request)
                     });
                  tcenv = (uu___147_11790.tcenv);
                  debug = (uu___147_11790.debug);
                  delta_level =
                    [FStar_TypeChecker_Env.Unfold
                       FStar_Syntax_Syntax.Delta_constant];
                  primitive_steps = (uu___147_11790.primitive_steps);
                  strong = (uu___147_11790.strong);
                  memoize_lazy = (uu___147_11790.memoize_lazy);
                  normalize_pure_lets = true
                }  in
              let uu____11798 = get_norm_request (norm cfg' env []) args  in
              (match uu____11798 with
               | FStar_Pervasives_Native.None  ->
                   let stack1 =
                     FStar_All.pipe_right stack
                       (FStar_List.fold_right
                          (fun uu____11829  ->
                             fun stack1  ->
                               match uu____11829 with
                               | (a,aq) ->
                                   let uu____11841 =
                                     let uu____11842 =
                                       let uu____11849 =
                                         let uu____11850 =
                                           let uu____11881 =
                                             FStar_Util.mk_ref
                                               FStar_Pervasives_Native.None
                                              in
                                           (env, a, uu____11881, false)  in
                                         Clos uu____11850  in
                                       (uu____11849, aq,
                                         (t1.FStar_Syntax_Syntax.pos))
                                        in
                                     Arg uu____11842  in
                                   uu____11841 :: stack1) args)
                      in
                   let uu____11962 =
                     log cfg
                       (fun uu____11965  ->
                          let uu____11966 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11966)
                      in
                   norm cfg env stack1 hd1
               | FStar_Pervasives_Native.Some (s,tm) ->
                   let delta_level =
                     let uu____11988 =
                       FStar_All.pipe_right s
                         (FStar_Util.for_some
                            (fun uu___88_11993  ->
                               match uu___88_11993 with
                               | UnfoldUntil uu____11994 -> true
                               | UnfoldOnly uu____11995 -> true
                               | UnfoldFully uu____11998 -> true
                               | uu____12001 -> false))
                        in
                     if uu____11988
                     then
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.Delta_constant]
                     else [FStar_TypeChecker_Env.NoDelta]  in
                   let cfg'1 =
                     let uu___149_12006 = cfg  in
                     let uu____12007 =
                       let uu___150_12008 = to_fsteps s  in
                       {
                         beta = (uu___150_12008.beta);
                         iota = (uu___150_12008.iota);
                         zeta = (uu___150_12008.zeta);
                         weak = (uu___150_12008.weak);
                         hnf = (uu___150_12008.hnf);
                         primops = (uu___150_12008.primops);
                         do_not_unfold_pure_lets =
                           (uu___150_12008.do_not_unfold_pure_lets);
                         unfold_until = (uu___150_12008.unfold_until);
                         unfold_only = (uu___150_12008.unfold_only);
                         unfold_fully = (uu___150_12008.unfold_fully);
                         unfold_attr = (uu___150_12008.unfold_attr);
                         unfold_tac = (uu___150_12008.unfold_tac);
                         pure_subterms_within_computations =
                           (uu___150_12008.pure_subterms_within_computations);
                         simplify = (uu___150_12008.simplify);
                         erase_universes = (uu___150_12008.erase_universes);
                         allow_unbound_universes =
                           (uu___150_12008.allow_unbound_universes);
                         reify_ = (uu___150_12008.reify_);
                         compress_uvars = (uu___150_12008.compress_uvars);
                         no_full_norm = (uu___150_12008.no_full_norm);
                         check_no_uvars = (uu___150_12008.check_no_uvars);
                         unmeta = (uu___150_12008.unmeta);
                         unascribe = (uu___150_12008.unascribe);
                         in_full_norm_request = true
                       }  in
                     {
                       steps = uu____12007;
                       tcenv = (uu___149_12006.tcenv);
                       debug = (uu___149_12006.debug);
                       delta_level;
                       primitive_steps = (uu___149_12006.primitive_steps);
                       strong = (uu___149_12006.strong);
                       memoize_lazy = (uu___149_12006.memoize_lazy);
                       normalize_pure_lets = true
                     }  in
                   let stack' =
                     let tail1 = (Cfg cfg) :: stack  in
                     if (cfg.debug).print_normalized
                     then
                       let uu____12017 =
                         let uu____12018 =
                           let uu____12023 = FStar_Util.now ()  in
                           (t1, uu____12023)  in
                         Debug uu____12018  in
                       uu____12017 :: tail1
                     else tail1  in
                   norm cfg'1 env stack' tm)
          | FStar_Syntax_Syntax.Tm_type u ->
              let u1 = norm_universe cfg env u  in
              let uu____12027 =
                mk (FStar_Syntax_Syntax.Tm_type u1)
                  t1.FStar_Syntax_Syntax.pos
                 in
              rebuild cfg env stack uu____12027
          | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
              if (cfg.steps).erase_universes
              then norm cfg env stack t'
              else
                (let us1 =
                   let uu____12036 =
                     let uu____12043 =
                       FStar_List.map (norm_universe cfg env) us  in
                     (uu____12043, (t1.FStar_Syntax_Syntax.pos))  in
                   UnivArgs uu____12036  in
                 let stack1 = us1 :: stack  in norm cfg env stack1 t')
          | FStar_Syntax_Syntax.Tm_fvar fv ->
              let qninfo =
                let uu____12053 = FStar_Syntax_Syntax.lid_of_fv fv  in
                FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12053  in
              let uu____12054 = FStar_TypeChecker_Env.qninfo_is_action qninfo
                 in
              if uu____12054
              then
                let b = should_reify cfg stack  in
                let uu____12056 =
                  log cfg
                    (fun uu____12060  ->
                       let uu____12061 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12062 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12061 uu____12062)
                   in
                (if b
                 then
                   let uu____12063 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____12063 t1 qninfo fv
                 else rebuild cfg env stack t1)
              else
                (let should_delta =
                   ((let uu____12071 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____12071) &&
                      (match qninfo with
                       | FStar_Pervasives_Native.Some
                           (FStar_Util.Inr
                            ({
                               FStar_Syntax_Syntax.sigel =
                                 FStar_Syntax_Syntax.Sig_let
                                 ((is_rec,uu____12084),uu____12085);
                               FStar_Syntax_Syntax.sigrng = uu____12086;
                               FStar_Syntax_Syntax.sigquals = qs;
                               FStar_Syntax_Syntax.sigmeta = uu____12088;
                               FStar_Syntax_Syntax.sigattrs = uu____12089;_},uu____12090),uu____12091)
                           ->
                           (Prims.op_Negation
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.HasMaskedEffect qs))
                             &&
                             ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                       | uu____12156 -> true))
                     &&
                     (FStar_All.pipe_right cfg.delta_level
                        (FStar_Util.for_some
                           (fun uu___89_12160  ->
                              match uu___89_12160 with
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
                   should_delta &&
                     (let attrs =
                        FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                      ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                         (let uu____12170 =
                            cases
                              (FStar_Util.for_some
                                 (FStar_Syntax_Util.attr_eq
                                    FStar_Syntax_Util.tac_opaque_attr)) false
                              attrs
                             in
                          Prims.op_Negation uu____12170))
                        &&
                        ((match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> true
                          | FStar_Pervasives_Native.Some lids ->
                              FStar_Util.for_some
                                (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                           ||
                           (match (attrs, ((cfg.steps).unfold_attr)) with
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.Some uu____12189) ->
                                false
                            | (FStar_Pervasives_Native.Some
                               ats,FStar_Pervasives_Native.Some ats') ->
                                FStar_Util.for_some
                                  (fun at  ->
                                     FStar_Util.for_some
                                       (FStar_Syntax_Util.attr_eq at) ats')
                                  ats
                            | (uu____12224,uu____12225) -> false)))
                    in
                 let uu____12242 =
                   match (cfg.steps).unfold_fully with
                   | FStar_Pervasives_Native.None  -> (should_delta1, false)
                   | FStar_Pervasives_Native.Some lids ->
                       let uu____12258 =
                         FStar_Util.for_some
                           (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                          in
                       if uu____12258 then (true, true) else (false, false)
                    in
                 match uu____12242 with
                 | (should_delta2,fully) ->
                     let uu____12266 =
                       log cfg
                         (fun uu____12271  ->
                            let uu____12272 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12273 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12274 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12272 uu____12273 uu____12274)
                        in
                     if should_delta2
                     then
                       let uu____12275 =
                         if fully
                         then
                           (((Cfg cfg) :: stack),
                             (let uu___151_12291 = cfg  in
                              {
                                steps =
                                  (let uu___152_12294 = cfg.steps  in
                                   {
                                     beta = (uu___152_12294.beta);
                                     iota = false;
                                     zeta = false;
                                     weak = false;
                                     hnf = false;
                                     primops = false;
                                     do_not_unfold_pure_lets =
                                       (uu___152_12294.do_not_unfold_pure_lets);
                                     unfold_until =
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.Delta_constant);
                                     unfold_only =
                                       FStar_Pervasives_Native.None;
                                     unfold_fully =
                                       FStar_Pervasives_Native.None;
                                     unfold_attr =
                                       (uu___152_12294.unfold_attr);
                                     unfold_tac = (uu___152_12294.unfold_tac);
                                     pure_subterms_within_computations =
                                       (uu___152_12294.pure_subterms_within_computations);
                                     simplify = false;
                                     erase_universes =
                                       (uu___152_12294.erase_universes);
                                     allow_unbound_universes =
                                       (uu___152_12294.allow_unbound_universes);
                                     reify_ = (uu___152_12294.reify_);
                                     compress_uvars =
                                       (uu___152_12294.compress_uvars);
                                     no_full_norm =
                                       (uu___152_12294.no_full_norm);
                                     check_no_uvars =
                                       (uu___152_12294.check_no_uvars);
                                     unmeta = (uu___152_12294.unmeta);
                                     unascribe = (uu___152_12294.unascribe);
                                     in_full_norm_request =
                                       (uu___152_12294.in_full_norm_request)
                                   });
                                tcenv = (uu___151_12291.tcenv);
                                debug = (uu___151_12291.debug);
                                delta_level = (uu___151_12291.delta_level);
                                primitive_steps =
                                  (uu___151_12291.primitive_steps);
                                strong = (uu___151_12291.strong);
                                memoize_lazy = (uu___151_12291.memoize_lazy);
                                normalize_pure_lets =
                                  (uu___151_12291.normalize_pure_lets)
                              }))
                         else (stack, cfg)  in
                       (match uu____12275 with
                        | (stack1,cfg1) ->
                            do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                     else rebuild cfg env stack t1)
          | FStar_Syntax_Syntax.Tm_bvar x ->
              let uu____12308 = lookup_bvar env x  in
              (match uu____12308 with
               | Univ uu____12309 ->
                   failwith
                     "Impossible: term variable is bound to a universe"
               | Dummy  -> failwith "Term variable not found"
               | Clos (env1,t0,r,fix) ->
                   if (Prims.op_Negation fix) || (cfg.steps).zeta
                   then
                     let uu____12358 = FStar_ST.op_Bang r  in
                     (match uu____12358 with
                      | FStar_Pervasives_Native.Some (env2,t') ->
                          let uu____12476 =
                            log cfg
                              (fun uu____12480  ->
                                 let uu____12481 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12482 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12481
                                   uu____12482)
                             in
                          let uu____12483 = maybe_weakly_reduced t'  in
                          if uu____12483
                          then
                            (match stack with
                             | [] when
                                 (cfg.steps).weak ||
                                   (cfg.steps).compress_uvars
                                 -> rebuild cfg env2 stack t'
                             | uu____12484 -> norm cfg env2 stack t')
                          else rebuild cfg env2 stack t'
                      | FStar_Pervasives_Native.None  ->
                          norm cfg env1 ((MemoLazy r) :: stack) t0)
                   else norm cfg env1 stack t0)
          | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
              (match stack with
               | (UnivArgs uu____12555)::uu____12556 ->
                   failwith
                     "Ill-typed term: universes cannot be applied to term abstraction"
               | (Match uu____12565)::uu____12566 ->
                   failwith
                     "Ill-typed term: cannot pattern match an abstraction"
               | (Arg (c,uu____12578,uu____12579))::stack_rest ->
                   (match c with
                    | Univ uu____12583 ->
                        norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                          stack_rest t1
                    | uu____12592 ->
                        (match bs with
                         | [] -> failwith "Impossible"
                         | b::[] ->
                             let uu____12610 =
                               log cfg
                                 (fun uu____12613  ->
                                    let uu____12614 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12614)
                                in
                             norm cfg (((FStar_Pervasives_Native.Some b), c)
                               :: env) stack_rest body
                         | b::tl1 ->
                             let uu____12651 =
                               log cfg
                                 (fun uu____12654  ->
                                    let uu____12655 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12655)
                                in
                             let body1 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_abs
                                    (tl1, body, lopt))
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             norm cfg (((FStar_Pervasives_Native.Some b), c)
                               :: env) stack_rest body1))
               | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
               | (MemoLazy r)::stack1 ->
                   let uu____12703 = set_memo cfg r (env, t1)  in
                   let uu____12730 =
                     log cfg
                       (fun uu____12733  ->
                          let uu____12734 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12734)
                      in
                   norm cfg env stack1 t1
               | (Debug uu____12735)::uu____12736 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_12746 = cfg.steps  in
                            {
                              beta = (uu___153_12746.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_12746.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_12746.unfold_until);
                              unfold_only = (uu___153_12746.unfold_only);
                              unfold_fully = (uu___153_12746.unfold_fully);
                              unfold_attr = (uu___153_12746.unfold_attr);
                              unfold_tac = (uu___153_12746.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_12746.erase_universes);
                              allow_unbound_universes =
                                (uu___153_12746.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_12746.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_12746.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_12746.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_12748 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_12748.tcenv);
                              debug = (uu___154_12748.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_12748.primitive_steps);
                              strong = (uu___154_12748.strong);
                              memoize_lazy = (uu___154_12748.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_12748.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____12750 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____12750 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____12792  -> dummy :: env1) env)
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
                                         let uu____12829 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____12829)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_12834 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_12834.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_12834.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____12835 -> lopt  in
                          let uu____12838 =
                            log cfg
                              (fun uu____12841  ->
                                 let uu____12842 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12842)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_12851 = cfg  in
                            {
                              steps = (uu___156_12851.steps);
                              tcenv = (uu___156_12851.tcenv);
                              debug = (uu___156_12851.debug);
                              delta_level = (uu___156_12851.delta_level);
                              primitive_steps =
                                (uu___156_12851.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_12851.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_12851.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (Meta uu____12862)::uu____12863 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_12875 = cfg.steps  in
                            {
                              beta = (uu___153_12875.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_12875.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_12875.unfold_until);
                              unfold_only = (uu___153_12875.unfold_only);
                              unfold_fully = (uu___153_12875.unfold_fully);
                              unfold_attr = (uu___153_12875.unfold_attr);
                              unfold_tac = (uu___153_12875.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_12875.erase_universes);
                              allow_unbound_universes =
                                (uu___153_12875.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_12875.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_12875.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_12875.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_12877 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_12877.tcenv);
                              debug = (uu___154_12877.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_12877.primitive_steps);
                              strong = (uu___154_12877.strong);
                              memoize_lazy = (uu___154_12877.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_12877.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____12879 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____12879 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____12921  -> dummy :: env1) env)
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
                                         let uu____12958 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____12958)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_12963 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_12963.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_12963.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____12964 -> lopt  in
                          let uu____12967 =
                            log cfg
                              (fun uu____12970  ->
                                 let uu____12971 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12971)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_12980 = cfg  in
                            {
                              steps = (uu___156_12980.steps);
                              tcenv = (uu___156_12980.tcenv);
                              debug = (uu___156_12980.debug);
                              delta_level = (uu___156_12980.delta_level);
                              primitive_steps =
                                (uu___156_12980.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_12980.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_12980.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (Let uu____12991)::uu____12992 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_13006 = cfg.steps  in
                            {
                              beta = (uu___153_13006.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_13006.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_13006.unfold_until);
                              unfold_only = (uu___153_13006.unfold_only);
                              unfold_fully = (uu___153_13006.unfold_fully);
                              unfold_attr = (uu___153_13006.unfold_attr);
                              unfold_tac = (uu___153_13006.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_13006.erase_universes);
                              allow_unbound_universes =
                                (uu___153_13006.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_13006.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_13006.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_13006.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_13008 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_13008.tcenv);
                              debug = (uu___154_13008.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_13008.primitive_steps);
                              strong = (uu___154_13008.strong);
                              memoize_lazy = (uu___154_13008.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_13008.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____13010 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____13010 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13052  -> dummy :: env1) env)
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
                                         let uu____13089 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13089)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13094 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13094.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13094.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13095 -> lopt  in
                          let uu____13098 =
                            log cfg
                              (fun uu____13101  ->
                                 let uu____13102 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13102)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13111 = cfg  in
                            {
                              steps = (uu___156_13111.steps);
                              tcenv = (uu___156_13111.tcenv);
                              debug = (uu___156_13111.debug);
                              delta_level = (uu___156_13111.delta_level);
                              primitive_steps =
                                (uu___156_13111.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13111.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13111.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (App uu____13122)::uu____13123 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_13137 = cfg.steps  in
                            {
                              beta = (uu___153_13137.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_13137.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_13137.unfold_until);
                              unfold_only = (uu___153_13137.unfold_only);
                              unfold_fully = (uu___153_13137.unfold_fully);
                              unfold_attr = (uu___153_13137.unfold_attr);
                              unfold_tac = (uu___153_13137.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_13137.erase_universes);
                              allow_unbound_universes =
                                (uu___153_13137.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_13137.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_13137.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_13137.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_13139 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_13139.tcenv);
                              debug = (uu___154_13139.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_13139.primitive_steps);
                              strong = (uu___154_13139.strong);
                              memoize_lazy = (uu___154_13139.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_13139.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____13141 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____13141 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13183  -> dummy :: env1) env)
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
                                         let uu____13220 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13220)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13225 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13225.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13225.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13226 -> lopt  in
                          let uu____13229 =
                            log cfg
                              (fun uu____13232  ->
                                 let uu____13233 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13233)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13242 = cfg  in
                            {
                              steps = (uu___156_13242.steps);
                              tcenv = (uu___156_13242.tcenv);
                              debug = (uu___156_13242.debug);
                              delta_level = (uu___156_13242.delta_level);
                              primitive_steps =
                                (uu___156_13242.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13242.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13242.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (Abs uu____13253)::uu____13254 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_13272 = cfg.steps  in
                            {
                              beta = (uu___153_13272.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_13272.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_13272.unfold_until);
                              unfold_only = (uu___153_13272.unfold_only);
                              unfold_fully = (uu___153_13272.unfold_fully);
                              unfold_attr = (uu___153_13272.unfold_attr);
                              unfold_tac = (uu___153_13272.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_13272.erase_universes);
                              allow_unbound_universes =
                                (uu___153_13272.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_13272.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_13272.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_13272.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_13274 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_13274.tcenv);
                              debug = (uu___154_13274.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_13274.primitive_steps);
                              strong = (uu___154_13274.strong);
                              memoize_lazy = (uu___154_13274.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_13274.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____13276 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____13276 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13318  -> dummy :: env1) env)
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
                                         let uu____13355 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13355)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13360 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13360.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13360.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13361 -> lopt  in
                          let uu____13364 =
                            log cfg
                              (fun uu____13367  ->
                                 let uu____13368 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13368)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13377 = cfg  in
                            {
                              steps = (uu___156_13377.steps);
                              tcenv = (uu___156_13377.tcenv);
                              debug = (uu___156_13377.debug);
                              delta_level = (uu___156_13377.delta_level);
                              primitive_steps =
                                (uu___156_13377.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13377.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13377.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | [] ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_13391 = cfg.steps  in
                            {
                              beta = (uu___153_13391.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_13391.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_13391.unfold_until);
                              unfold_only = (uu___153_13391.unfold_only);
                              unfold_fully = (uu___153_13391.unfold_fully);
                              unfold_attr = (uu___153_13391.unfold_attr);
                              unfold_tac = (uu___153_13391.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_13391.erase_universes);
                              allow_unbound_universes =
                                (uu___153_13391.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_13391.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_13391.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_13391.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_13393 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_13393.tcenv);
                              debug = (uu___154_13393.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_13393.primitive_steps);
                              strong = (uu___154_13393.strong);
                              memoize_lazy = (uu___154_13393.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_13393.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____13395 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____13395 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13437  -> dummy :: env1) env)
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
                                         let uu____13474 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13474)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13479 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13479.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13479.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13480 -> lopt  in
                          let uu____13483 =
                            log cfg
                              (fun uu____13486  ->
                                 let uu____13487 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13487)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13496 = cfg  in
                            {
                              steps = (uu___156_13496.steps);
                              tcenv = (uu___156_13496.tcenv);
                              debug = (uu___156_13496.debug);
                              delta_level = (uu___156_13496.delta_level);
                              primitive_steps =
                                (uu___156_13496.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13496.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13496.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1))
          | FStar_Syntax_Syntax.Tm_app (head1,args) ->
              let stack1 =
                FStar_All.pipe_right stack
                  (FStar_List.fold_right
                     (fun uu____13545  ->
                        fun stack1  ->
                          match uu____13545 with
                          | (a,aq) ->
                              let uu____13557 =
                                let uu____13558 =
                                  let uu____13565 =
                                    let uu____13566 =
                                      let uu____13597 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (env, a, uu____13597, false)  in
                                    Clos uu____13566  in
                                  (uu____13565, aq,
                                    (t1.FStar_Syntax_Syntax.pos))
                                   in
                                Arg uu____13558  in
                              uu____13557 :: stack1) args)
                 in
              let uu____13678 =
                log cfg
                  (fun uu____13681  ->
                     let uu____13682 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13682)
                 in
              norm cfg env stack1 head1
          | FStar_Syntax_Syntax.Tm_refine (x,f) ->
              if (cfg.steps).weak
              then
                (match (env, stack) with
                 | ([],[]) ->
                     let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                     let t2 =
                       mk
                         (FStar_Syntax_Syntax.Tm_refine
                            ((let uu___157_13718 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___157_13718.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___157_13718.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), f)) t1.FStar_Syntax_Syntax.pos
                        in
                     rebuild cfg env stack t2
                 | uu____13719 ->
                     let uu____13724 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13724)
              else
                (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                 let uu____13727 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 match uu____13727 with
                 | (closing,f1) ->
                     let f2 = norm cfg (dummy :: env) [] f1  in
                     let t2 =
                       let uu____13758 =
                         let uu____13759 =
                           let uu____13766 =
                             FStar_Syntax_Subst.close closing f2  in
                           ((let uu___158_13768 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_13768.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_13768.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t_x
                             }), uu____13766)
                            in
                         FStar_Syntax_Syntax.Tm_refine uu____13759  in
                       mk uu____13758 t1.FStar_Syntax_Syntax.pos  in
                     rebuild cfg env stack t2)
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (cfg.steps).weak
              then
                let uu____13787 = closure_as_term cfg env t1  in
                rebuild cfg env stack uu____13787
              else
                (let uu____13789 = FStar_Syntax_Subst.open_comp bs c  in
                 match uu____13789 with
                 | (bs1,c1) ->
                     let c2 =
                       let uu____13797 =
                         FStar_All.pipe_right bs1
                           (FStar_List.fold_left
                              (fun env1  -> fun uu____13821  -> dummy :: env1)
                              env)
                          in
                       norm_comp cfg uu____13797 c1  in
                     let t2 =
                       let uu____13843 = norm_binders cfg env bs1  in
                       FStar_Syntax_Util.arrow uu____13843 c2  in
                     rebuild cfg env stack t2)
          | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
              (cfg.steps).unascribe -> norm cfg env stack t11
          | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
              (match stack with
               | (Match uu____13954)::uu____13955 ->
                   let uu____13966 =
                     log cfg
                       (fun uu____13968  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | (Arg uu____13969)::uu____13970 ->
                   let uu____13979 =
                     log cfg
                       (fun uu____13981  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | (App
                   (uu____13982,{
                                  FStar_Syntax_Syntax.n =
                                    FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reify );
                                  FStar_Syntax_Syntax.pos = uu____13983;
                                  FStar_Syntax_Syntax.vars = uu____13984;_},uu____13985,uu____13986))::uu____13987
                   ->
                   let uu____13994 =
                     log cfg
                       (fun uu____13996  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | (MemoLazy uu____13997)::uu____13998 ->
                   let uu____14007 =
                     log cfg
                       (fun uu____14009  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | uu____14010 ->
                   let uu____14011 =
                     log cfg
                       (fun uu____14013  ->
                          FStar_Util.print_string "+++ Keeping ascription \n")
                      in
                   let t12 = norm cfg env [] t11  in
                   let uu____14015 =
                     log cfg
                       (fun uu____14017  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n")
                      in
                   let tc1 =
                     match tc with
                     | FStar_Util.Inl t2 ->
                         let uu____14034 = norm cfg env [] t2  in
                         FStar_Util.Inl uu____14034
                     | FStar_Util.Inr c ->
                         let uu____14042 = norm_comp cfg env c  in
                         FStar_Util.Inr uu____14042
                      in
                   let tacopt1 = FStar_Util.map_opt tacopt (norm cfg env [])
                      in
                   (match stack with
                    | (Cfg cfg1)::stack1 ->
                        let t2 =
                          let uu____14055 =
                            let uu____14056 =
                              let uu____14083 =
                                FStar_Syntax_Util.unascribe t12  in
                              (uu____14083, (tc1, tacopt1), l)  in
                            FStar_Syntax_Syntax.Tm_ascribed uu____14056  in
                          mk uu____14055 t1.FStar_Syntax_Syntax.pos  in
                        norm cfg1 env stack1 t2
                    | uu____14102 ->
                        let uu____14103 =
                          let uu____14104 =
                            let uu____14105 =
                              let uu____14132 =
                                FStar_Syntax_Util.unascribe t12  in
                              (uu____14132, (tc1, tacopt1), l)  in
                            FStar_Syntax_Syntax.Tm_ascribed uu____14105  in
                          mk uu____14104 t1.FStar_Syntax_Syntax.pos  in
                        rebuild cfg env stack uu____14103))
          | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
              let stack1 =
                (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos))) ::
                stack  in
              let cfg1 =
                if (cfg.steps).iota
                then
                  let uu___159_14209 = cfg  in
                  {
                    steps =
                      (let uu___160_14212 = cfg.steps  in
                       {
                         beta = (uu___160_14212.beta);
                         iota = (uu___160_14212.iota);
                         zeta = (uu___160_14212.zeta);
                         weak = true;
                         hnf = (uu___160_14212.hnf);
                         primops = (uu___160_14212.primops);
                         do_not_unfold_pure_lets =
                           (uu___160_14212.do_not_unfold_pure_lets);
                         unfold_until = (uu___160_14212.unfold_until);
                         unfold_only = (uu___160_14212.unfold_only);
                         unfold_fully = (uu___160_14212.unfold_fully);
                         unfold_attr = (uu___160_14212.unfold_attr);
                         unfold_tac = (uu___160_14212.unfold_tac);
                         pure_subterms_within_computations =
                           (uu___160_14212.pure_subterms_within_computations);
                         simplify = (uu___160_14212.simplify);
                         erase_universes = (uu___160_14212.erase_universes);
                         allow_unbound_universes =
                           (uu___160_14212.allow_unbound_universes);
                         reify_ = (uu___160_14212.reify_);
                         compress_uvars = (uu___160_14212.compress_uvars);
                         no_full_norm = (uu___160_14212.no_full_norm);
                         check_no_uvars = (uu___160_14212.check_no_uvars);
                         unmeta = (uu___160_14212.unmeta);
                         unascribe = (uu___160_14212.unascribe);
                         in_full_norm_request =
                           (uu___160_14212.in_full_norm_request)
                       });
                    tcenv = (uu___159_14209.tcenv);
                    debug = (uu___159_14209.debug);
                    delta_level = (uu___159_14209.delta_level);
                    primitive_steps = (uu___159_14209.primitive_steps);
                    strong = (uu___159_14209.strong);
                    memoize_lazy = (uu___159_14209.memoize_lazy);
                    normalize_pure_lets =
                      (uu___159_14209.normalize_pure_lets)
                  }
                else cfg  in
              norm cfg1 env stack1 head1
          | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
              (FStar_Syntax_Syntax.is_top_level lbs) &&
                (cfg.steps).compress_uvars
              ->
              let lbs1 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu____14248 =
                          FStar_Syntax_Subst.univ_var_opening
                            lb.FStar_Syntax_Syntax.lbunivs
                           in
                        match uu____14248 with
                        | (openings,lbunivs) ->
                            let cfg1 =
                              let uu___161_14268 = cfg  in
                              let uu____14269 =
                                FStar_TypeChecker_Env.push_univ_vars
                                  cfg.tcenv lbunivs
                                 in
                              {
                                steps = (uu___161_14268.steps);
                                tcenv = uu____14269;
                                debug = (uu___161_14268.debug);
                                delta_level = (uu___161_14268.delta_level);
                                primitive_steps =
                                  (uu___161_14268.primitive_steps);
                                strong = (uu___161_14268.strong);
                                memoize_lazy = (uu___161_14268.memoize_lazy);
                                normalize_pure_lets =
                                  (uu___161_14268.normalize_pure_lets)
                              }  in
                            let norm1 t2 =
                              let uu____14276 =
                                let uu____14277 =
                                  FStar_Syntax_Subst.subst openings t2  in
                                norm cfg1 env [] uu____14277  in
                              FStar_Syntax_Subst.close_univ_vars lbunivs
                                uu____14276
                               in
                            let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                               in
                            let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                               in
                            let uu___162_14280 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___162_14280.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = lbunivs;
                              FStar_Syntax_Syntax.lbtyp = lbtyp;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___162_14280.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___162_14280.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___162_14280.FStar_Syntax_Syntax.lbpos)
                            }))
                 in
              let uu____14281 =
                mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                  t1.FStar_Syntax_Syntax.pos
                 in
              rebuild cfg env stack uu____14281
          | FStar_Syntax_Syntax.Tm_let
              ((uu____14292,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____14293;
                              FStar_Syntax_Syntax.lbunivs = uu____14294;
                              FStar_Syntax_Syntax.lbtyp = uu____14295;
                              FStar_Syntax_Syntax.lbeff = uu____14296;
                              FStar_Syntax_Syntax.lbdef = uu____14297;
                              FStar_Syntax_Syntax.lbattrs = uu____14298;
                              FStar_Syntax_Syntax.lbpos = uu____14299;_}::uu____14300),uu____14301)
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
              let n1 =
                FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                  lb.FStar_Syntax_Syntax.lbeff
                 in
              let uu____14341 =
                (Prims.op_Negation (cfg.steps).do_not_unfold_pure_lets) &&
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
              if uu____14341
              then
                let binder =
                  let uu____14343 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.mk_binder uu____14343  in
                let env1 =
                  let uu____14353 =
                    let uu____14360 =
                      let uu____14361 =
                        let uu____14392 =
                          FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                        (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14392,
                          false)
                         in
                      Clos uu____14361  in
                    ((FStar_Pervasives_Native.Some binder), uu____14360)  in
                  uu____14353 :: env  in
                let uu____14483 =
                  log cfg
                    (fun uu____14485  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n")
                   in
                norm cfg env1 stack body
              else
                if (cfg.steps).weak
                then
                  (let uu____14487 =
                     log cfg
                       (fun uu____14489  ->
                          FStar_Util.print_string "+++ Not touching Tm_let\n")
                      in
                   let uu____14490 = closure_as_term cfg env t1  in
                   rebuild cfg env stack uu____14490)
                else
                  (let uu____14492 =
                     let uu____14497 =
                       let uu____14498 =
                         let uu____14499 =
                           FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                             FStar_Util.left
                            in
                         FStar_All.pipe_right uu____14499
                           FStar_Syntax_Syntax.mk_binder
                          in
                       [uu____14498]  in
                     FStar_Syntax_Subst.open_term uu____14497 body  in
                   match uu____14492 with
                   | (bs,body1) ->
                       let uu____14506 =
                         log cfg
                           (fun uu____14508  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type")
                          in
                       let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                          in
                       let lbname =
                         let x =
                           let uu____14516 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____14516  in
                         FStar_Util.Inl
                           (let uu___163_14526 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___163_14526.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___163_14526.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            })
                          in
                       let uu____14527 =
                         log cfg
                           (fun uu____14529  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- definiens\n")
                          in
                       let lb1 =
                         let uu___164_14531 = lb  in
                         let uu____14532 =
                           norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                         {
                           FStar_Syntax_Syntax.lbname = lbname;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___164_14531.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = ty;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___164_14531.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = uu____14532;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___164_14531.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___164_14531.FStar_Syntax_Syntax.lbpos)
                         }  in
                       let env' =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun env1  -> fun uu____14567  -> dummy :: env1)
                              env)
                          in
                       let stack1 = (Cfg cfg) :: stack  in
                       let cfg1 =
                         let uu___165_14590 = cfg  in
                         {
                           steps = (uu___165_14590.steps);
                           tcenv = (uu___165_14590.tcenv);
                           debug = (uu___165_14590.debug);
                           delta_level = (uu___165_14590.delta_level);
                           primitive_steps = (uu___165_14590.primitive_steps);
                           strong = true;
                           memoize_lazy = (uu___165_14590.memoize_lazy);
                           normalize_pure_lets =
                             (uu___165_14590.normalize_pure_lets)
                         }  in
                       let uu____14591 =
                         log cfg1
                           (fun uu____14593  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n")
                          in
                       norm cfg1 env'
                         ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                         :: stack1) body1)
          | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
              (cfg.steps).compress_uvars ||
                ((Prims.op_Negation (cfg.steps).zeta) &&
                   (cfg.steps).pure_subterms_within_computations)
              ->
              let uu____14610 = FStar_Syntax_Subst.open_let_rec lbs body  in
              (match uu____14610 with
               | (lbs1,body1) ->
                   let lbs2 =
                     FStar_List.map
                       (fun lb  ->
                          let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let uu____14646 =
                              let uu___166_14647 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_14647.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___166_14647.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }  in
                            FStar_Util.Inl uu____14646  in
                          let uu____14648 =
                            FStar_Syntax_Util.abs_formals
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          match uu____14648 with
                          | (xs,def_body,lopt) ->
                              let xs1 = norm_binders cfg env xs  in
                              let env1 =
                                let uu____14674 =
                                  FStar_List.map (fun uu____14690  -> dummy)
                                    lbs1
                                   in
                                let uu____14691 =
                                  let uu____14700 =
                                    FStar_List.map
                                      (fun uu____14720  -> dummy) xs1
                                     in
                                  FStar_List.append uu____14700 env  in
                                FStar_List.append uu____14674 uu____14691  in
                              let def_body1 = norm cfg env1 [] def_body  in
                              let lopt1 =
                                match lopt with
                                | FStar_Pervasives_Native.Some rc ->
                                    let uu____14744 =
                                      let uu___167_14745 = rc  in
                                      let uu____14746 =
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (norm cfg env1 [])
                                         in
                                      {
                                        FStar_Syntax_Syntax.residual_effect =
                                          (uu___167_14745.FStar_Syntax_Syntax.residual_effect);
                                        FStar_Syntax_Syntax.residual_typ =
                                          uu____14746;
                                        FStar_Syntax_Syntax.residual_flags =
                                          (uu___167_14745.FStar_Syntax_Syntax.residual_flags)
                                      }  in
                                    FStar_Pervasives_Native.Some uu____14744
                                | uu____14753 -> lopt  in
                              let def =
                                FStar_Syntax_Util.abs xs1 def_body1 lopt1  in
                              let uu___168_14757 = lb  in
                              {
                                FStar_Syntax_Syntax.lbname = lbname;
                                FStar_Syntax_Syntax.lbunivs =
                                  (uu___168_14757.FStar_Syntax_Syntax.lbunivs);
                                FStar_Syntax_Syntax.lbtyp = ty;
                                FStar_Syntax_Syntax.lbeff =
                                  (uu___168_14757.FStar_Syntax_Syntax.lbeff);
                                FStar_Syntax_Syntax.lbdef = def;
                                FStar_Syntax_Syntax.lbattrs =
                                  (uu___168_14757.FStar_Syntax_Syntax.lbattrs);
                                FStar_Syntax_Syntax.lbpos =
                                  (uu___168_14757.FStar_Syntax_Syntax.lbpos)
                              }) lbs1
                      in
                   let env' =
                     let uu____14767 =
                       FStar_List.map (fun uu____14783  -> dummy) lbs2  in
                     FStar_List.append uu____14767 env  in
                   let body2 = norm cfg env' [] body1  in
                   let uu____14791 =
                     FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                   (match uu____14791 with
                    | (lbs3,body3) ->
                        let t2 =
                          let uu___169_14807 = t1  in
                          {
                            FStar_Syntax_Syntax.n =
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs3), body3));
                            FStar_Syntax_Syntax.pos =
                              (uu___169_14807.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___169_14807.FStar_Syntax_Syntax.vars)
                          }  in
                        rebuild cfg env stack t2))
          | FStar_Syntax_Syntax.Tm_let (lbs,body) when
              Prims.op_Negation (cfg.steps).zeta ->
              let uu____14834 = closure_as_term cfg env t1  in
              rebuild cfg env stack uu____14834
          | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
              let uu____14853 =
                FStar_List.fold_right
                  (fun lb  ->
                     fun uu____14929  ->
                       match uu____14929 with
                       | (rec_env,memos,i) ->
                           let bv =
                             let uu___170_15050 =
                               FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___170_15050.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index = i;
                               FStar_Syntax_Syntax.sort =
                                 (uu___170_15050.FStar_Syntax_Syntax.sort)
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
              (match uu____14853 with
               | (rec_env,memos,uu____15263) ->
                   let uu____15316 =
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
                            let uu____15639 =
                              let uu____15646 =
                                let uu____15647 =
                                  let uu____15678 =
                                    FStar_Util.mk_ref
                                      FStar_Pervasives_Native.None
                                     in
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                    uu____15678, false)
                                   in
                                Clos uu____15647  in
                              (FStar_Pervasives_Native.None, uu____15646)  in
                            uu____15639 :: env1)
                       (FStar_Pervasives_Native.snd lbs) env
                      in
                   norm cfg body_env stack body)
          | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
              let uu____15785 =
                log cfg
                  (fun uu____15788  ->
                     let uu____15789 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15789)
                 in
              (match m with
               | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                   reduce_impure_comp cfg env stack head1 (FStar_Util.Inl m1)
                     t2
               | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                   reduce_impure_comp cfg env stack head1
                     (FStar_Util.Inr (m1, m')) t2
               | uu____15811 ->
                   if (cfg.steps).unmeta
                   then norm cfg env stack head1
                   else
                     (match stack with
                      | uu____15813::uu____15814 ->
                          (match m with
                           | FStar_Syntax_Syntax.Meta_labeled
                               (l,r,uu____15819) ->
                               norm cfg env ((Meta (env, m, r)) :: stack)
                                 head1
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let args1 = norm_pattern_args cfg env args  in
                               norm cfg env
                                 ((Meta
                                     (env,
                                       (FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                       (t1.FStar_Syntax_Syntax.pos))) ::
                                 stack) head1
                           | uu____15842 -> norm cfg env stack head1)
                      | [] ->
                          let head2 = norm cfg env [] head1  in
                          let m1 =
                            match m with
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let uu____15856 =
                                  norm_pattern_args cfg env args  in
                                FStar_Syntax_Syntax.Meta_pattern uu____15856
                            | uu____15867 -> m  in
                          let t2 =
                            mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack t2))
          | FStar_Syntax_Syntax.Tm_delayed uu____15871 ->
              let t2 = FStar_Syntax_Subst.compress t1  in
              norm cfg env stack t2
          | FStar_Syntax_Syntax.Tm_uvar uu____15897 ->
              let t2 = FStar_Syntax_Subst.compress t1  in
              (match t2.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uvar uu____15915 ->
                   if (cfg.steps).check_no_uvars
                   then
                     let uu____15932 =
                       let uu____15933 =
                         FStar_Range.string_of_range
                           t2.FStar_Syntax_Syntax.pos
                          in
                       let uu____15934 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format2
                         "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                         uu____15933 uu____15934
                        in
                     failwith uu____15932
                   else rebuild cfg env stack t2
               | uu____15936 -> norm cfg env stack t2)

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
                let uu____15946 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____15946  in
              let uu____15947 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15947 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15958 =
                    log cfg
                      (fun uu____15960  ->
                         FStar_Util.print "Tm_fvar case 2\n" [])
                     in
                  rebuild cfg env stack t0
              | FStar_Pervasives_Native.Some (us,t) ->
                  let uu____15967 =
                    log cfg
                      (fun uu____15971  ->
                         let uu____15972 =
                           FStar_Syntax_Print.term_to_string t0  in
                         let uu____15973 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 ">>> Unfolded %s to %s\n"
                           uu____15972 uu____15973)
                     in
                  let t1 =
                    if
                      ((cfg.steps).unfold_until =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Delta_constant))
                        && (Prims.op_Negation (cfg.steps).unfold_tac)
                    then t
                    else
                      (let uu____15978 =
                         FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_Syntax_Subst.set_use_range uu____15978 t)
                     in
                  let n1 = FStar_List.length us  in
                  if n1 > (Prims.parse_int "0")
                  then
                    (match stack with
                     | (UnivArgs (us',uu____15987))::stack1 ->
                         let env1 =
                           FStar_All.pipe_right us'
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun u  ->
                                     (FStar_Pervasives_Native.None, (Univ u))
                                     :: env1) env)
                            in
                         norm cfg env1 stack1 t1
                     | uu____16042 when
                         (cfg.steps).erase_universes ||
                           (cfg.steps).allow_unbound_universes
                         -> norm cfg env stack t1
                     | uu____16045 ->
                         let uu____16048 =
                           let uu____16049 =
                             FStar_Syntax_Print.lid_to_string
                               (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           FStar_Util.format1
                             "Impossible: missing universe instantiation on %s"
                             uu____16049
                            in
                         failwith uu____16048)
                  else norm cfg env stack t1

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
                  let new_steps =
                    [PureSubtermsWithinComputations;
                    Primops;
                    AllowUnboundUniverses;
                    EraseUniverses;
                    Exclude Zeta;
                    Inlining]  in
                  let uu___171_16073 = cfg  in
                  let uu____16074 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16074;
                    tcenv = (uu___171_16073.tcenv);
                    debug = (uu___171_16073.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_16073.primitive_steps);
                    strong = (uu___171_16073.strong);
                    memoize_lazy = (uu___171_16073.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_16073.normalize_pure_lets)
                  }
                else
                  (let uu___172_16076 = cfg  in
                   {
                     steps =
                       (let uu___173_16079 = cfg.steps  in
                        {
                          beta = (uu___173_16079.beta);
                          iota = (uu___173_16079.iota);
                          zeta = false;
                          weak = (uu___173_16079.weak);
                          hnf = (uu___173_16079.hnf);
                          primops = (uu___173_16079.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_16079.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_16079.unfold_until);
                          unfold_only = (uu___173_16079.unfold_only);
                          unfold_fully = (uu___173_16079.unfold_fully);
                          unfold_attr = (uu___173_16079.unfold_attr);
                          unfold_tac = (uu___173_16079.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_16079.pure_subterms_within_computations);
                          simplify = (uu___173_16079.simplify);
                          erase_universes = (uu___173_16079.erase_universes);
                          allow_unbound_universes =
                            (uu___173_16079.allow_unbound_universes);
                          reify_ = (uu___173_16079.reify_);
                          compress_uvars = (uu___173_16079.compress_uvars);
                          no_full_norm = (uu___173_16079.no_full_norm);
                          check_no_uvars = (uu___173_16079.check_no_uvars);
                          unmeta = (uu___173_16079.unmeta);
                          unascribe = (uu___173_16079.unascribe);
                          in_full_norm_request =
                            (uu___173_16079.in_full_norm_request)
                        });
                     tcenv = (uu___172_16076.tcenv);
                     debug = (uu___172_16076.debug);
                     delta_level = (uu___172_16076.delta_level);
                     primitive_steps = (uu___172_16076.primitive_steps);
                     strong = (uu___172_16076.strong);
                     memoize_lazy = (uu___172_16076.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_16076.normalize_pure_lets)
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
                ((Meta (env, metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
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
                let uu____16105 =
                  log cfg
                    (fun uu____16109  ->
                       let uu____16110 = FStar_Syntax_Print.tag_of_term head2
                          in
                       let uu____16111 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print2 "Reifying: (%s) %s\n" uu____16110
                         uu____16111)
                   in
                let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                let uu____16113 =
                  let uu____16114 = FStar_Syntax_Subst.compress head3  in
                  uu____16114.FStar_Syntax_Syntax.n  in
                match uu____16113 with
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let ed =
                      let uu____16132 =
                        FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                      FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                        uu____16132
                       in
                    let uu____16133 = ed.FStar_Syntax_Syntax.bind_repr  in
                    (match uu____16133 with
                     | (uu____16134,bind_repr) ->
                         (match lb.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____16140 ->
                              failwith "Cannot reify a top-level let binding"
                          | FStar_Util.Inl x ->
                              let is_return e =
                                let uu____16150 =
                                  let uu____16151 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16151.FStar_Syntax_Syntax.n  in
                                match uu____16150 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e1,FStar_Syntax_Syntax.Meta_monadic
                                     (uu____16157,uu____16158))
                                    ->
                                    let uu____16167 =
                                      let uu____16168 =
                                        FStar_Syntax_Subst.compress e1  in
                                      uu____16168.FStar_Syntax_Syntax.n  in
                                    (match uu____16167 with
                                     | FStar_Syntax_Syntax.Tm_meta
                                         (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                          (uu____16174,msrc,uu____16176))
                                         when
                                         FStar_Syntax_Util.is_pure_effect
                                           msrc
                                         ->
                                         let uu____16185 =
                                           FStar_Syntax_Subst.compress e2  in
                                         FStar_Pervasives_Native.Some
                                           uu____16185
                                     | uu____16186 ->
                                         FStar_Pervasives_Native.None)
                                | uu____16187 -> FStar_Pervasives_Native.None
                                 in
                              let uu____16188 =
                                is_return lb.FStar_Syntax_Syntax.lbdef  in
                              (match uu____16188 with
                               | FStar_Pervasives_Native.Some e ->
                                   let lb1 =
                                     let uu___174_16193 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___174_16193.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___174_16193.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___174_16193.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         FStar_Parser_Const.effect_PURE_lid;
                                       FStar_Syntax_Syntax.lbdef = e;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___174_16193.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___174_16193.FStar_Syntax_Syntax.lbpos)
                                     }  in
                                   let uu____16194 = FStar_List.tl stack  in
                                   let uu____16195 =
                                     let uu____16196 =
                                       let uu____16203 =
                                         let uu____16204 =
                                           let uu____16217 =
                                             FStar_Syntax_Util.mk_reify body
                                              in
                                           ((false, [lb1]), uu____16217)  in
                                         FStar_Syntax_Syntax.Tm_let
                                           uu____16204
                                          in
                                       FStar_Syntax_Syntax.mk uu____16203  in
                                     uu____16196 FStar_Pervasives_Native.None
                                       head3.FStar_Syntax_Syntax.pos
                                      in
                                   norm cfg env uu____16194 uu____16195
                               | FStar_Pervasives_Native.None  ->
                                   let uu____16233 =
                                     let uu____16234 = is_return body  in
                                     match uu____16234 with
                                     | FStar_Pervasives_Native.Some
                                         {
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_bvar y;
                                           FStar_Syntax_Syntax.pos =
                                             uu____16238;
                                           FStar_Syntax_Syntax.vars =
                                             uu____16239;_}
                                         -> FStar_Syntax_Syntax.bv_eq x y
                                     | uu____16244 -> false  in
                                   if uu____16233
                                   then
                                     norm cfg env stack
                                       lb.FStar_Syntax_Syntax.lbdef
                                   else
                                     (let rng = head3.FStar_Syntax_Syntax.pos
                                         in
                                      let head4 =
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
                                        let uu____16267 =
                                          let uu____16274 =
                                            let uu____16275 =
                                              let uu____16292 =
                                                let uu____16295 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x
                                                   in
                                                [uu____16295]  in
                                              (uu____16292, body1,
                                                (FStar_Pervasives_Native.Some
                                                   body_rc))
                                               in
                                            FStar_Syntax_Syntax.Tm_abs
                                              uu____16275
                                             in
                                          FStar_Syntax_Syntax.mk uu____16274
                                           in
                                        uu____16267
                                          FStar_Pervasives_Native.None
                                          body1.FStar_Syntax_Syntax.pos
                                         in
                                      let close1 = closure_as_term cfg env
                                         in
                                      let bind_inst =
                                        let uu____16313 =
                                          let uu____16314 =
                                            FStar_Syntax_Subst.compress
                                              bind_repr
                                             in
                                          uu____16314.FStar_Syntax_Syntax.n
                                           in
                                        match uu____16313 with
                                        | FStar_Syntax_Syntax.Tm_uinst
                                            (bind1,uu____16320::uu____16321::[])
                                            ->
                                            let uu____16328 =
                                              let uu____16335 =
                                                let uu____16336 =
                                                  let uu____16343 =
                                                    let uu____16346 =
                                                      let uu____16347 =
                                                        close1
                                                          lb.FStar_Syntax_Syntax.lbtyp
                                                         in
                                                      (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                        cfg.tcenv uu____16347
                                                       in
                                                    let uu____16348 =
                                                      let uu____16351 =
                                                        let uu____16352 =
                                                          close1 t  in
                                                        (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.tcenv
                                                          uu____16352
                                                         in
                                                      [uu____16351]  in
                                                    uu____16346 ::
                                                      uu____16348
                                                     in
                                                  (bind1, uu____16343)  in
                                                FStar_Syntax_Syntax.Tm_uinst
                                                  uu____16336
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____16335
                                               in
                                            uu____16328
                                              FStar_Pervasives_Native.None
                                              rng
                                        | uu____16360 ->
                                            failwith
                                              "NIY : Reification of indexed effects"
                                         in
                                      let maybe_range_arg =
                                        let uu____16366 =
                                          FStar_Util.for_some
                                            (FStar_Syntax_Util.attr_eq
                                               FStar_Syntax_Util.dm4f_bind_range_attr)
                                            ed.FStar_Syntax_Syntax.eff_attrs
                                           in
                                        if uu____16366
                                        then
                                          let uu____16369 =
                                            let uu____16370 =
                                              FStar_Syntax_Embeddings.embed
                                                FStar_Syntax_Embeddings.e_range
                                                lb.FStar_Syntax_Syntax.lbpos
                                                lb.FStar_Syntax_Syntax.lbpos
                                               in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____16370
                                             in
                                          let uu____16371 =
                                            let uu____16374 =
                                              let uu____16375 =
                                                FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_range
                                                  body2.FStar_Syntax_Syntax.pos
                                                  body2.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____16375
                                               in
                                            [uu____16374]  in
                                          uu____16369 :: uu____16371
                                        else []  in
                                      let reified =
                                        let uu____16380 =
                                          let uu____16387 =
                                            let uu____16388 =
                                              let uu____16403 =
                                                let uu____16406 =
                                                  let uu____16409 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  let uu____16410 =
                                                    let uu____16413 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    [uu____16413]  in
                                                  uu____16409 :: uu____16410
                                                   in
                                                let uu____16414 =
                                                  let uu____16417 =
                                                    let uu____16420 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        FStar_Syntax_Syntax.tun
                                                       in
                                                    let uu____16421 =
                                                      let uu____16424 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          head4
                                                         in
                                                      let uu____16425 =
                                                        let uu____16428 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            FStar_Syntax_Syntax.tun
                                                           in
                                                        let uu____16429 =
                                                          let uu____16432 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              body2
                                                             in
                                                          [uu____16432]  in
                                                        uu____16428 ::
                                                          uu____16429
                                                         in
                                                      uu____16424 ::
                                                        uu____16425
                                                       in
                                                    uu____16420 ::
                                                      uu____16421
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____16417
                                                   in
                                                FStar_List.append uu____16406
                                                  uu____16414
                                                 in
                                              (bind_inst, uu____16403)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____16388
                                             in
                                          FStar_Syntax_Syntax.mk uu____16387
                                           in
                                        uu____16380
                                          FStar_Pervasives_Native.None rng
                                         in
                                      let uu____16440 =
                                        log cfg
                                          (fun uu____16444  ->
                                             let uu____16445 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____16446 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____16445 uu____16446)
                                         in
                                      let uu____16447 = FStar_List.tl stack
                                         in
                                      norm cfg env uu____16447 reified))))
                | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                    let ed =
                      let uu____16471 =
                        FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                      FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                        uu____16471
                       in
                    let uu____16472 = ed.FStar_Syntax_Syntax.bind_repr  in
                    (match uu____16472 with
                     | (uu____16473,bind_repr) ->
                         let maybe_unfold_action head4 =
                           let maybe_extract_fv t1 =
                             let t2 =
                               let uu____16512 =
                                 let uu____16513 =
                                   FStar_Syntax_Subst.compress t1  in
                                 uu____16513.FStar_Syntax_Syntax.n  in
                               match uu____16512 with
                               | FStar_Syntax_Syntax.Tm_uinst
                                   (t2,uu____16519) -> t2
                               | uu____16524 -> head4  in
                             let uu____16525 =
                               let uu____16526 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____16526.FStar_Syntax_Syntax.n  in
                             match uu____16525 with
                             | FStar_Syntax_Syntax.Tm_fvar x ->
                                 FStar_Pervasives_Native.Some x
                             | uu____16532 -> FStar_Pervasives_Native.None
                              in
                           let uu____16533 = maybe_extract_fv head4  in
                           match uu____16533 with
                           | FStar_Pervasives_Native.Some x when
                               let uu____16543 =
                                 FStar_Syntax_Syntax.lid_of_fv x  in
                               FStar_TypeChecker_Env.is_action cfg.tcenv
                                 uu____16543
                               ->
                               let head5 = norm cfg env [] head4  in
                               let action_unfolded =
                                 let uu____16548 = maybe_extract_fv head5  in
                                 match uu____16548 with
                                 | FStar_Pervasives_Native.Some uu____16553
                                     -> FStar_Pervasives_Native.Some true
                                 | uu____16554 ->
                                     FStar_Pervasives_Native.Some false
                                  in
                               (head5, action_unfolded)
                           | uu____16559 ->
                               (head4, FStar_Pervasives_Native.None)
                            in
                         let uu____16566 =
                           let is_arg_impure uu____16576 =
                             match uu____16576 with
                             | (e,q) ->
                                 let uu____16583 =
                                   let uu____16584 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16584.FStar_Syntax_Syntax.n  in
                                 (match uu____16583 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                       (m1,m2,t'))
                                      ->
                                      let uu____16599 =
                                        FStar_Syntax_Util.is_pure_effect m1
                                         in
                                      Prims.op_Negation uu____16599
                                  | uu____16600 -> false)
                              in
                           let uu____16601 =
                             let uu____16602 =
                               let uu____16609 =
                                 FStar_Syntax_Syntax.as_arg head_app  in
                               uu____16609 :: args  in
                             FStar_Util.for_some is_arg_impure uu____16602
                              in
                           if uu____16601
                           then
                             let uu____16614 =
                               let uu____16615 =
                                 FStar_Syntax_Print.term_to_string head3  in
                               FStar_Util.format1
                                 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                 uu____16615
                                in
                             failwith uu____16614
                           else ()  in
                         let uu____16617 = maybe_unfold_action head_app  in
                         (match uu____16617 with
                          | (head_app1,found_action) ->
                              let mk1 tm =
                                FStar_Syntax_Syntax.mk tm
                                  FStar_Pervasives_Native.None
                                  head3.FStar_Syntax_Syntax.pos
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
                              let uu____16656 =
                                log cfg
                                  (fun uu____16660  ->
                                     let uu____16661 =
                                       FStar_Syntax_Print.term_to_string
                                         head0
                                        in
                                     let uu____16662 =
                                       FStar_Syntax_Print.term_to_string
                                         body1
                                        in
                                     FStar_Util.print2
                                       "Reified (2) <%s> to %s\n" uu____16661
                                       uu____16662)
                                 in
                              let uu____16663 = FStar_List.tl stack  in
                              norm cfg env uu____16663 body1))
                | FStar_Syntax_Syntax.Tm_meta
                    (e,FStar_Syntax_Syntax.Meta_monadic uu____16665) ->
                    do_reify_monadic fallback cfg env stack e m t
                | FStar_Syntax_Syntax.Tm_meta
                    (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                    ->
                    let lifted =
                      let uu____16689 = closure_as_term cfg env t'  in
                      reify_lift cfg e msrc mtgt uu____16689  in
                    let uu____16690 =
                      log cfg
                        (fun uu____16693  ->
                           let uu____16694 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16694)
                       in
                    let uu____16695 = FStar_List.tl stack  in
                    norm cfg env uu____16695 lifted
                | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                    let branches1 =
                      FStar_All.pipe_right branches
                        (FStar_List.map
                           (fun uu____16816  ->
                              match uu____16816 with
                              | (pat,wopt,tm) ->
                                  let uu____16864 =
                                    FStar_Syntax_Util.mk_reify tm  in
                                  (pat, wopt, uu____16864)))
                       in
                    let tm =
                      mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                        head3.FStar_Syntax_Syntax.pos
                       in
                    let uu____16896 = FStar_List.tl stack  in
                    norm cfg env uu____16896 tm
                | uu____16897 -> fallback ()

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
            let uu____16906 =
              log cfg
                (fun uu____16911  ->
                   let uu____16912 = FStar_Ident.string_of_lid msrc  in
                   let uu____16913 = FStar_Ident.string_of_lid mtgt  in
                   let uu____16914 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print3 "Reifying lift %s -> %s: %s\n"
                     uu____16912 uu____16913 uu____16914)
               in
            let uu____16915 =
              (FStar_Syntax_Util.is_pure_effect msrc) ||
                (FStar_Syntax_Util.is_div_effect msrc)
               in
            if uu____16915
            then
              let ed =
                let uu____16917 =
                  FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                FStar_TypeChecker_Env.get_effect_decl env uu____16917  in
              let uu____16918 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____16918 with
              | (uu____16919,return_repr) ->
                  let return_inst =
                    let uu____16928 =
                      let uu____16929 =
                        FStar_Syntax_Subst.compress return_repr  in
                      uu____16929.FStar_Syntax_Syntax.n  in
                    match uu____16928 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16935::[]) ->
                        let uu____16942 =
                          let uu____16949 =
                            let uu____16950 =
                              let uu____16957 =
                                let uu____16960 =
                                  env.FStar_TypeChecker_Env.universe_of env t
                                   in
                                [uu____16960]  in
                              (return_tm, uu____16957)  in
                            FStar_Syntax_Syntax.Tm_uinst uu____16950  in
                          FStar_Syntax_Syntax.mk uu____16949  in
                        uu____16942 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16968 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  let uu____16971 =
                    let uu____16978 =
                      let uu____16979 =
                        let uu____16994 =
                          let uu____16997 = FStar_Syntax_Syntax.as_arg t  in
                          let uu____16998 =
                            let uu____17001 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____17001]  in
                          uu____16997 :: uu____16998  in
                        (return_inst, uu____16994)  in
                      FStar_Syntax_Syntax.Tm_app uu____16979  in
                    FStar_Syntax_Syntax.mk uu____16978  in
                  uu____16971 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____17010 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17010 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17013 =
                     let uu____17014 = FStar_Ident.text_of_lid msrc  in
                     let uu____17015 = FStar_Ident.text_of_lid mtgt  in
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       uu____17014 uu____17015
                      in
                   failwith uu____17013
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17016;
                     FStar_TypeChecker_Env.mtarget = uu____17017;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17018;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17040 =
                     let uu____17041 = FStar_Ident.text_of_lid msrc  in
                     let uu____17042 = FStar_Ident.text_of_lid mtgt  in
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       uu____17041 uu____17042
                      in
                   failwith uu____17040
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17043;
                     FStar_TypeChecker_Env.mtarget = uu____17044;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17045;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17080 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17081 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17080 t FStar_Syntax_Syntax.tun uu____17081)

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
                (fun uu____17137  ->
                   match uu____17137 with
                   | (a,imp) ->
                       let uu____17148 = norm cfg env [] a  in
                       (uu____17148, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let uu____17152 =
          log cfg
            (fun uu____17156  ->
               let uu____17157 = FStar_Syntax_Print.comp_to_string comp  in
               let uu____17158 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
                 uu____17157 uu____17158)
           in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let t1 = norm cfg env [] t  in
            let uopt1 =
              match uopt with
              | FStar_Pervasives_Native.Some u ->
                  let uu____17182 = norm_universe cfg env u  in
                  FStar_All.pipe_left
                    (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                    uu____17182
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
               in
            let uu___175_17185 = comp  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t1, uopt1));
              FStar_Syntax_Syntax.pos =
                (uu___175_17185.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_17185.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let t1 = norm cfg env [] t  in
            let uopt1 =
              match uopt with
              | FStar_Pervasives_Native.Some u ->
                  let uu____17205 = norm_universe cfg env u  in
                  FStar_All.pipe_left
                    (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                    uu____17205
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
               in
            let uu___176_17208 = comp  in
            {
              FStar_Syntax_Syntax.n =
                (FStar_Syntax_Syntax.GTotal (t1, uopt1));
              FStar_Syntax_Syntax.pos =
                (uu___176_17208.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_17208.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args =
              FStar_List.mapi
                (fun idx  ->
                   fun uu____17243  ->
                     match uu____17243 with
                     | (a,i) ->
                         let uu____17254 = norm cfg env [] a  in
                         (uu____17254, i))
               in
            let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_17272  ->
                      match uu___90_17272 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17276 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____17276
                      | f -> f))
               in
            let comp_univs =
              FStar_List.map (norm_universe cfg env)
                ct.FStar_Syntax_Syntax.comp_univs
               in
            let result_typ =
              norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
            let uu___177_17284 = comp  in
            {
              FStar_Syntax_Syntax.n =
                (FStar_Syntax_Syntax.Comp
                   (let uu___178_17287 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_univs = comp_univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___178_17287.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ = result_typ;
                      FStar_Syntax_Syntax.effect_args = effect_args;
                      FStar_Syntax_Syntax.flags = flags1
                    }));
              FStar_Syntax_Syntax.pos =
                (uu___177_17284.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_17284.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17290  ->
        match uu____17290 with
        | (x,imp) ->
            let uu____17293 =
              let uu___179_17294 = x  in
              let uu____17295 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_17294.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_17294.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17295
              }  in
            (uu____17293, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17301 =
          FStar_List.fold_left
            (fun uu____17319  ->
               fun b  ->
                 match uu____17319 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17301 with | (nbs,uu____17359) -> FStar_List.rev nbs

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
            let uu____17375 =
              let uu___180_17376 = rc  in
              let uu____17377 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_17376.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17377;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_17376.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17375
        | uu____17384 -> lopt

and (maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          let uu____17404 =
            if (cfg.debug).b380
            then
              let uu____17405 = FStar_Syntax_Print.term_to_string tm  in
              let uu____17406 = FStar_Syntax_Print.term_to_string tm'  in
              FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
                (if (cfg.steps).simplify then "" else "NOT ") uu____17405
                uu____17406
            else ()  in
          tm'

and (maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____17426 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17426
          then tm1
          else
            (let w t =
               let uu___181_17440 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_17440.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_17440.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17451 =
                 let uu____17452 = FStar_Syntax_Util.unmeta t  in
                 uu____17452.FStar_Syntax_Syntax.n  in
               match uu____17451 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17459 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17508)::args1,(bv,uu____17511)::bs1) ->
                   let uu____17545 =
                     let uu____17546 = FStar_Syntax_Subst.compress t  in
                     uu____17546.FStar_Syntax_Syntax.n  in
                   (match uu____17545 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17550 -> false)
               | ([],[]) -> true
               | (uu____17571,uu____17572) -> false  in
             let is_applied bs t =
               let uu____17612 = FStar_Syntax_Util.head_and_args' t  in
               match uu____17612 with
               | (hd1,args) ->
                   let uu____17645 =
                     let uu____17646 = FStar_Syntax_Subst.compress hd1  in
                     uu____17646.FStar_Syntax_Syntax.n  in
                   (match uu____17645 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____17652 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____17668 = FStar_Syntax_Util.is_squash t  in
               match uu____17668 with
               | FStar_Pervasives_Native.Some (uu____17679,t') ->
                   is_applied bs t'
               | uu____17691 ->
                   let uu____17700 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____17700 with
                    | FStar_Pervasives_Native.Some (uu____17711,t') ->
                        is_applied bs t'
                    | uu____17723 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____17742 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17742 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17749)::(q,uu____17751)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____17786 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____17786 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____17791 =
                          let uu____17792 = FStar_Syntax_Subst.compress p  in
                          uu____17792.FStar_Syntax_Syntax.n  in
                        (match uu____17791 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17798 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____17798
                         | uu____17799 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____17802)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____17827 =
                          let uu____17828 = FStar_Syntax_Subst.compress p1
                             in
                          uu____17828.FStar_Syntax_Syntax.n  in
                        (match uu____17827 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17834 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____17834
                         | uu____17835 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____17839 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____17839 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____17844 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____17844 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17851 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17851
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____17854)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____17879 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____17879 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17886 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17886
                              | uu____17887 -> FStar_Pervasives_Native.None)
                         | uu____17890 -> FStar_Pervasives_Native.None)
                    | uu____17893 -> FStar_Pervasives_Native.None)
               | uu____17896 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17909 =
                 let uu____17910 = FStar_Syntax_Subst.compress phi  in
                 uu____17910.FStar_Syntax_Syntax.n  in
               match uu____17909 with
               | FStar_Syntax_Syntax.Tm_match (uu____17915,br::brs) ->
                   let uu____17982 = br  in
                   (match uu____17982 with
                    | (uu____17999,uu____18000,e) ->
                        let r =
                          let uu____18021 = simp_t e  in
                          match uu____18021 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18027 =
                                FStar_List.for_all
                                  (fun uu____18045  ->
                                     match uu____18045 with
                                     | (uu____18058,uu____18059,e') ->
                                         let uu____18073 = simp_t e'  in
                                         uu____18073 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18027
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18081 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18088 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18088
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18113 =
                 match uu____18113 with
                 | (t1,q) ->
                     let uu____18126 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18126 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18154 -> (t1, q))
                  in
               let uu____18163 = FStar_Syntax_Util.head_and_args t  in
               match uu____18163 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18227 =
                 let uu____18228 = FStar_Syntax_Util.unmeta ty  in
                 uu____18228.FStar_Syntax_Syntax.n  in
               match uu____18227 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18232) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18237,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18257 -> false  in
             let simplify1 arg =
               let uu____18282 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18282, arg)  in
             let uu____18291 = is_quantified_const tm1  in
             match uu____18291 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18295 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18295
             | FStar_Pervasives_Native.None  ->
                 let uu____18296 =
                   let uu____18297 = FStar_Syntax_Subst.compress tm1  in
                   uu____18297.FStar_Syntax_Syntax.n  in
                 (match uu____18296 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18301;
                              FStar_Syntax_Syntax.vars = uu____18302;_},uu____18303);
                         FStar_Syntax_Syntax.pos = uu____18304;
                         FStar_Syntax_Syntax.vars = uu____18305;_},args)
                      ->
                      let uu____18331 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18331
                      then
                        let uu____18332 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18332 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18379)::
                             (uu____18380,(arg,uu____18382))::[] ->
                             maybe_auto_squash arg
                         | (uu____18431,(arg,uu____18433))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18434)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18483)::uu____18484::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18535::(FStar_Pervasives_Native.Some (false
                                         ),uu____18536)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18587 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18601 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18601
                         then
                           let uu____18602 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18602 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18649)::uu____18650::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18701::(FStar_Pervasives_Native.Some (true
                                           ),uu____18702)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18753)::(uu____18754,(arg,uu____18756))::[]
                               -> maybe_auto_squash arg
                           | (uu____18805,(arg,uu____18807))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18808)::[]
                               -> maybe_auto_squash arg
                           | uu____18857 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18871 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18871
                            then
                              let uu____18872 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18872 with
                              | uu____18919::(FStar_Pervasives_Native.Some
                                              (true ),uu____18920)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18971)::uu____18972::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19023)::(uu____19024,(arg,uu____19026))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19075,(p,uu____19077))::(uu____19078,
                                                                (q,uu____19080))::[]
                                  ->
                                  let uu____19127 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19127
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19129 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19143 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19143
                               then
                                 let uu____19144 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19144 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19191)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19192)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19243)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19244)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19295)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19296)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19347)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19348)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19399,(arg,uu____19401))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19402)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19451)::(uu____19452,(arg,uu____19454))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19503,(arg,uu____19505))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19506)::[]
                                     ->
                                     let uu____19555 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19555
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19556)::(uu____19557,(arg,uu____19559))::[]
                                     ->
                                     let uu____19608 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19608
                                 | (uu____19609,(p,uu____19611))::(uu____19612,
                                                                   (q,uu____19614))::[]
                                     ->
                                     let uu____19661 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19661
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19663 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19677 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19677
                                  then
                                    let uu____19678 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19678 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19725)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19756)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19787 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19801 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19801
                                     then
                                       match args with
                                       | (t,uu____19803)::[] ->
                                           let uu____19820 =
                                             let uu____19821 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19821.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19820 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19824::[],body,uu____19826)
                                                ->
                                                let uu____19853 = simp_t body
                                                   in
                                                (match uu____19853 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19856 -> tm1)
                                            | uu____19859 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19861))::(t,uu____19863)::[]
                                           ->
                                           let uu____19902 =
                                             let uu____19903 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19903.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19902 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19906::[],body,uu____19908)
                                                ->
                                                let uu____19935 = simp_t body
                                                   in
                                                (match uu____19935 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19938 -> tm1)
                                            | uu____19941 -> tm1)
                                       | uu____19942 -> tm1
                                     else
                                       (let uu____19952 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19952
                                        then
                                          match args with
                                          | (t,uu____19954)::[] ->
                                              let uu____19971 =
                                                let uu____19972 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19972.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19971 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19975::[],body,uu____19977)
                                                   ->
                                                   let uu____20004 =
                                                     simp_t body  in
                                                   (match uu____20004 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20007 -> tm1)
                                               | uu____20010 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20012))::(t,uu____20014)::[]
                                              ->
                                              let uu____20053 =
                                                let uu____20054 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20054.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20053 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20057::[],body,uu____20059)
                                                   ->
                                                   let uu____20086 =
                                                     simp_t body  in
                                                   (match uu____20086 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____20089 -> tm1)
                                               | uu____20092 -> tm1)
                                          | uu____20093 -> tm1
                                        else
                                          (let uu____20103 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20103
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20104;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20105;_},uu____20106)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20123;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20124;_},uu____20125)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20142 -> tm1
                                           else
                                             (let uu____20152 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20152 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20172 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20182;
                         FStar_Syntax_Syntax.vars = uu____20183;_},args)
                      ->
                      let uu____20205 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20205
                      then
                        let uu____20206 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20206 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20253)::
                             (uu____20254,(arg,uu____20256))::[] ->
                             maybe_auto_squash arg
                         | (uu____20305,(arg,uu____20307))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20308)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20357)::uu____20358::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20409::(FStar_Pervasives_Native.Some (false
                                         ),uu____20410)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20461 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20475 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20475
                         then
                           let uu____20476 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20476 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20523)::uu____20524::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20575::(FStar_Pervasives_Native.Some (true
                                           ),uu____20576)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20627)::(uu____20628,(arg,uu____20630))::[]
                               -> maybe_auto_squash arg
                           | (uu____20679,(arg,uu____20681))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20682)::[]
                               -> maybe_auto_squash arg
                           | uu____20731 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20745 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20745
                            then
                              let uu____20746 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20746 with
                              | uu____20793::(FStar_Pervasives_Native.Some
                                              (true ),uu____20794)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20845)::uu____20846::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20897)::(uu____20898,(arg,uu____20900))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20949,(p,uu____20951))::(uu____20952,
                                                                (q,uu____20954))::[]
                                  ->
                                  let uu____21001 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21001
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21003 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21017 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21017
                               then
                                 let uu____21018 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21018 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21065)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21066)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21117)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21118)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21169)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21170)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21221)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21222)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21273,(arg,uu____21275))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21276)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21325)::(uu____21326,(arg,uu____21328))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21377,(arg,uu____21379))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21380)::[]
                                     ->
                                     let uu____21429 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21429
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21430)::(uu____21431,(arg,uu____21433))::[]
                                     ->
                                     let uu____21482 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21482
                                 | (uu____21483,(p,uu____21485))::(uu____21486,
                                                                   (q,uu____21488))::[]
                                     ->
                                     let uu____21535 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21535
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21537 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21551 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21551
                                  then
                                    let uu____21552 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21552 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21599)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21630)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21661 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21675 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21675
                                     then
                                       match args with
                                       | (t,uu____21677)::[] ->
                                           let uu____21694 =
                                             let uu____21695 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21695.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21694 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21698::[],body,uu____21700)
                                                ->
                                                let uu____21727 = simp_t body
                                                   in
                                                (match uu____21727 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21730 -> tm1)
                                            | uu____21733 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21735))::(t,uu____21737)::[]
                                           ->
                                           let uu____21776 =
                                             let uu____21777 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21777.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21776 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21780::[],body,uu____21782)
                                                ->
                                                let uu____21809 = simp_t body
                                                   in
                                                (match uu____21809 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21812 -> tm1)
                                            | uu____21815 -> tm1)
                                       | uu____21816 -> tm1
                                     else
                                       (let uu____21826 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21826
                                        then
                                          match args with
                                          | (t,uu____21828)::[] ->
                                              let uu____21845 =
                                                let uu____21846 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21846.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21845 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21849::[],body,uu____21851)
                                                   ->
                                                   let uu____21878 =
                                                     simp_t body  in
                                                   (match uu____21878 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21881 -> tm1)
                                               | uu____21884 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21886))::(t,uu____21888)::[]
                                              ->
                                              let uu____21927 =
                                                let uu____21928 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21928.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21927 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21931::[],body,uu____21933)
                                                   ->
                                                   let uu____21960 =
                                                     simp_t body  in
                                                   (match uu____21960 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____21963 -> tm1)
                                               | uu____21966 -> tm1)
                                          | uu____21967 -> tm1
                                        else
                                          (let uu____21977 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21977
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21978;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21979;_},uu____21980)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21997;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21998;_},uu____21999)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22016 -> tm1
                                           else
                                             (let uu____22026 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22026 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22046 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22061 = simp_t t  in
                      (match uu____22061 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22064 ->
                      let uu____22087 = is_const_match tm1  in
                      (match uu____22087 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22090 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let uu____22095 =
            log cfg
              (fun uu____22100  ->
                 let uu____22101 =
                   let uu____22102 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____22103 = FStar_Syntax_Print.term_to_string t  in
                   let uu____22104 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____22111 =
                     let uu____22112 =
                       let uu____22115 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____22115
                        in
                     stack_to_string uu____22112  in
                   FStar_Util.print4
                     ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                     uu____22102 uu____22103 uu____22104 uu____22111
                    in
                 let uu____22138 =
                   FStar_TypeChecker_Env.debug cfg.tcenv
                     (FStar_Options.Other "NormRebuild")
                    in
                 if uu____22138
                 then
                   let uu____22139 = FStar_Syntax_Util.unbound_variables t
                      in
                   match uu____22139 with
                   | [] -> ()
                   | bvs ->
                       let uu____22145 =
                         let uu____22146 = FStar_Syntax_Print.tag_of_term t
                            in
                         let uu____22147 =
                           FStar_Syntax_Print.term_to_string t  in
                         let uu____22148 =
                           let uu____22149 =
                             FStar_All.pipe_right bvs
                               (FStar_List.map
                                  FStar_Syntax_Print.bv_to_string)
                              in
                           FStar_All.pipe_right uu____22149
                             (FStar_String.concat ", ")
                            in
                         FStar_Util.print3
                           "!!! Rebuild (%s) %s, free vars=%s\n" uu____22146
                           uu____22147 uu____22148
                          in
                       failwith "DIE!"
                 else ())
             in
          let t1 = maybe_simplify cfg env stack t  in
          match stack with
          | [] -> t1
          | (Debug (tm,time_then))::stack1 ->
              let uu____22165 =
                if (cfg.debug).print_normalized
                then
                  let time_now = FStar_Util.now ()  in
                  let uu____22167 =
                    let uu____22168 =
                      let uu____22169 =
                        FStar_Util.time_diff time_then time_now  in
                      FStar_Pervasives_Native.snd uu____22169  in
                    FStar_Util.string_of_int uu____22168  in
                  let uu____22174 = FStar_Syntax_Print.term_to_string tm  in
                  let uu____22175 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____22167 uu____22174 uu____22175
                else ()  in
              rebuild cfg env stack1 t1
          | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
          | (Meta (uu____22181,m,r))::stack1 ->
              let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
              rebuild cfg env stack1 t2
          | (MemoLazy r)::stack1 ->
              let uu____22200 = set_memo cfg r (env, t1)  in
              let uu____22227 =
                log cfg
                  (fun uu____22230  ->
                     let uu____22231 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22231)
                 in
              rebuild cfg env stack1 t1
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
              let uu____22267 =
                let uu___182_22268 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___182_22268.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___182_22268.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack1 uu____22267
          | (Arg (Univ uu____22269,uu____22270,uu____22271))::uu____22272 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____22275,uu____22276))::uu____22277 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack1 ->
              let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
              rebuild cfg env stack1 t2
          | (Arg (Clos (env_arg,tm,uu____22292,uu____22293),aq,r))::stack1
              when
              let uu____22343 = head_of t1  in
              FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22343 ->
              let t2 =
                let uu____22347 =
                  let uu____22352 =
                    let uu____22353 = closure_as_term cfg env_arg tm  in
                    (uu____22353, aq)  in
                  FStar_Syntax_Syntax.extend_app t1 uu____22352  in
                uu____22347 FStar_Pervasives_Native.None r  in
              rebuild cfg env stack1 t2
          | (Arg (Clos (env_arg,tm,m,uu____22359),aq,r))::stack1 ->
              let uu____22409 =
                log cfg
                  (fun uu____22412  ->
                     let uu____22413 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22413)
                 in
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
                (let uu____22423 = FStar_ST.op_Bang m  in
                 match uu____22423 with
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
                 | FStar_Pervasives_Native.Some (uu____22564,a) ->
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (a, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2)
          | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
              let t0 = t1  in
              let fallback msg uu____22615 =
                let uu____22616 =
                  log cfg
                    (fun uu____22619  ->
                       let uu____22620 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.print2 "Not reifying%s: %s\n" msg
                         uu____22620)
                   in
                let t2 =
                  FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                    FStar_Pervasives_Native.None r
                   in
                rebuild cfg env1 stack' t2  in
              let uu____22624 =
                let uu____22625 = FStar_Syntax_Subst.compress t1  in
                uu____22625.FStar_Syntax_Syntax.n  in
              (match uu____22624 with
               | FStar_Syntax_Syntax.Tm_meta
                   (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                   do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
               | FStar_Syntax_Syntax.Tm_meta
                   (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                   ->
                   let lifted =
                     let uu____22652 = closure_as_term cfg env1 ty  in
                     reify_lift cfg t2 msrc mtgt uu____22652  in
                   let uu____22653 =
                     log cfg
                       (fun uu____22656  ->
                          let uu____22657 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22657)
                      in
                   let uu____22658 = FStar_List.tl stack  in
                   norm cfg env1 uu____22658 lifted
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____22659);
                      FStar_Syntax_Syntax.pos = uu____22660;
                      FStar_Syntax_Syntax.vars = uu____22661;_},(e,uu____22663)::[])
                   -> norm cfg env1 stack' e
               | FStar_Syntax_Syntax.Tm_app uu____22692 when
                   (cfg.steps).primops ->
                   let uu____22707 = FStar_Syntax_Util.head_and_args t1  in
                   (match uu____22707 with
                    | (hd1,args) ->
                        let uu____22744 =
                          let uu____22745 = FStar_Syntax_Util.un_uinst hd1
                             in
                          uu____22745.FStar_Syntax_Syntax.n  in
                        (match uu____22744 with
                         | FStar_Syntax_Syntax.Tm_fvar fv ->
                             let uu____22749 = find_prim_step cfg fv  in
                             (match uu____22749 with
                              | FStar_Pervasives_Native.Some
                                  { name = uu____22752; arity = uu____22753;
                                    auto_reflect =
                                      FStar_Pervasives_Native.Some n1;
                                    strong_reduction_ok = uu____22755;
                                    requires_binder_substitution =
                                      uu____22756;
                                    interpretation = uu____22757;_}
                                  when (FStar_List.length args) = n1 ->
                                  norm cfg env1 stack' t1
                              | uu____22772 -> fallback " (3)" ())
                         | uu____22775 -> fallback " (4)" ()))
               | uu____22776 -> fallback " (2)" ())
          | (App (env1,head1,aq,r))::stack1 ->
              let t2 =
                FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                  FStar_Pervasives_Native.None r
                 in
              rebuild cfg env1 stack1 t2
          | (Match (env',branches,cfg1,r))::stack1 ->
              let uu____22794 =
                log cfg1
                  (fun uu____22797  ->
                     let uu____22798 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22798)
                 in
              let scrutinee_env = env  in
              let env1 = env'  in
              let scrutinee = t1  in
              let norm_and_rebuild_match uu____22807 =
                let uu____22808 =
                  log cfg1
                    (fun uu____22812  ->
                       let uu____22813 =
                         FStar_Syntax_Print.term_to_string scrutinee  in
                       let uu____22814 =
                         let uu____22815 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____22832  ->
                                   match uu____22832 with
                                   | (p,uu____22842,uu____22843) ->
                                       FStar_Syntax_Print.pat_to_string p))
                            in
                         FStar_All.pipe_right uu____22815
                           (FStar_String.concat "\n\t")
                          in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____22813 uu____22814)
                   in
                let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                let cfg_exclude_zeta =
                  let new_delta =
                    FStar_All.pipe_right cfg1.delta_level
                      (FStar_List.filter
                         (fun uu___91_22860  ->
                            match uu___91_22860 with
                            | FStar_TypeChecker_Env.Inlining  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | uu____22861 -> false))
                     in
                  let steps =
                    let uu___183_22863 = cfg1.steps  in
                    {
                      beta = (uu___183_22863.beta);
                      iota = (uu___183_22863.iota);
                      zeta = false;
                      weak = (uu___183_22863.weak);
                      hnf = (uu___183_22863.hnf);
                      primops = (uu___183_22863.primops);
                      do_not_unfold_pure_lets =
                        (uu___183_22863.do_not_unfold_pure_lets);
                      unfold_until = FStar_Pervasives_Native.None;
                      unfold_only = FStar_Pervasives_Native.None;
                      unfold_fully = (uu___183_22863.unfold_fully);
                      unfold_attr = FStar_Pervasives_Native.None;
                      unfold_tac = false;
                      pure_subterms_within_computations =
                        (uu___183_22863.pure_subterms_within_computations);
                      simplify = (uu___183_22863.simplify);
                      erase_universes = (uu___183_22863.erase_universes);
                      allow_unbound_universes =
                        (uu___183_22863.allow_unbound_universes);
                      reify_ = (uu___183_22863.reify_);
                      compress_uvars = (uu___183_22863.compress_uvars);
                      no_full_norm = (uu___183_22863.no_full_norm);
                      check_no_uvars = (uu___183_22863.check_no_uvars);
                      unmeta = (uu___183_22863.unmeta);
                      unascribe = (uu___183_22863.unascribe);
                      in_full_norm_request =
                        (uu___183_22863.in_full_norm_request)
                    }  in
                  let uu___184_22868 = cfg1  in
                  {
                    steps;
                    tcenv = (uu___184_22868.tcenv);
                    debug = (uu___184_22868.debug);
                    delta_level = new_delta;
                    primitive_steps = (uu___184_22868.primitive_steps);
                    strong = true;
                    memoize_lazy = (uu___184_22868.memoize_lazy);
                    normalize_pure_lets =
                      (uu___184_22868.normalize_pure_lets)
                  }  in
                let norm_or_whnf env2 t2 =
                  if whnf
                  then closure_as_term cfg_exclude_zeta env2 t2
                  else norm cfg_exclude_zeta env2 [] t2  in
                let rec norm_pat env2 p =
                  match p.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_constant uu____22908 -> (p, env2)
                  | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                      let uu____22929 =
                        FStar_All.pipe_right pats
                          (FStar_List.fold_left
                             (fun uu____22989  ->
                                fun uu____22990  ->
                                  match (uu____22989, uu____22990) with
                                  | ((pats1,env3),(p1,b)) ->
                                      let uu____23081 = norm_pat env3 p1  in
                                      (match uu____23081 with
                                       | (p2,env4) ->
                                           (((p2, b) :: pats1), env4)))
                             ([], env2))
                         in
                      (match uu____22929 with
                       | (pats1,env3) ->
                           ((let uu___185_23163 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_cons
                                    (fv, (FStar_List.rev pats1)));
                               FStar_Syntax_Syntax.p =
                                 (uu___185_23163.FStar_Syntax_Syntax.p)
                             }), env3))
                  | FStar_Syntax_Syntax.Pat_var x ->
                      let x1 =
                        let uu___186_23182 = x  in
                        let uu____23183 =
                          norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___186_23182.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___186_23182.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____23183
                        }  in
                      ((let uu___187_23197 = p  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var x1);
                          FStar_Syntax_Syntax.p =
                            (uu___187_23197.FStar_Syntax_Syntax.p)
                        }), (dummy :: env2))
                  | FStar_Syntax_Syntax.Pat_wild x ->
                      let x1 =
                        let uu___188_23208 = x  in
                        let uu____23209 =
                          norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___188_23208.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___188_23208.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____23209
                        }  in
                      ((let uu___189_23223 = p  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild x1);
                          FStar_Syntax_Syntax.p =
                            (uu___189_23223.FStar_Syntax_Syntax.p)
                        }), (dummy :: env2))
                  | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                      let x1 =
                        let uu___190_23239 = x  in
                        let uu____23240 =
                          norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___190_23239.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___190_23239.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____23240
                        }  in
                      let t3 = norm_or_whnf env2 t2  in
                      ((let uu___191_23247 = p  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                          FStar_Syntax_Syntax.p =
                            (uu___191_23247.FStar_Syntax_Syntax.p)
                        }), env2)
                   in
                let branches1 =
                  match env1 with
                  | [] when whnf -> branches
                  | uu____23257 ->
                      FStar_All.pipe_right branches
                        (FStar_List.map
                           (fun branch1  ->
                              let uu____23271 =
                                FStar_Syntax_Subst.open_branch branch1  in
                              match uu____23271 with
                              | (p,wopt,e) ->
                                  let uu____23291 = norm_pat env1 p  in
                                  (match uu____23291 with
                                   | (p1,env2) ->
                                       let wopt1 =
                                         match wopt with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____23316 =
                                               norm_or_whnf env2 w  in
                                             FStar_Pervasives_Native.Some
                                               uu____23316
                                          in
                                       let e1 = norm_or_whnf env2 e  in
                                       FStar_Syntax_Util.branch
                                         (p1, wopt1, e1))))
                   in
                let scrutinee1 =
                  let uu____23323 =
                    (((cfg1.steps).iota &&
                        (Prims.op_Negation (cfg1.steps).weak))
                       && (Prims.op_Negation (cfg1.steps).compress_uvars))
                      && (maybe_weakly_reduced scrutinee)
                     in
                  if uu____23323
                  then norm cfg1 scrutinee_env [] scrutinee
                  else scrutinee  in
                let uu____23325 =
                  mk (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1)) r
                   in
                rebuild cfg1 env1 stack1 uu____23325  in
              let rec is_cons head1 =
                let uu____23332 =
                  let uu____23333 = FStar_Syntax_Subst.compress head1  in
                  uu____23333.FStar_Syntax_Syntax.n  in
                match uu____23332 with
                | FStar_Syntax_Syntax.Tm_uinst (h,uu____23337) -> is_cons h
                | FStar_Syntax_Syntax.Tm_constant uu____23342 -> true
                | FStar_Syntax_Syntax.Tm_fvar
                    { FStar_Syntax_Syntax.fv_name = uu____23343;
                      FStar_Syntax_Syntax.fv_delta = uu____23344;
                      FStar_Syntax_Syntax.fv_qual =
                        FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Data_ctor );_}
                    -> true
                | FStar_Syntax_Syntax.Tm_fvar
                    { FStar_Syntax_Syntax.fv_name = uu____23345;
                      FStar_Syntax_Syntax.fv_delta = uu____23346;
                      FStar_Syntax_Syntax.fv_qual =
                        FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_ctor uu____23347);_}
                    -> true
                | uu____23354 -> false  in
              let guard_when_clause wopt b rest =
                match wopt with
                | FStar_Pervasives_Native.None  -> b
                | FStar_Pervasives_Native.Some w ->
                    let then_branch = b  in
                    let else_branch =
                      mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r
                       in
                    FStar_Syntax_Util.if_then_else w then_branch else_branch
                 in
              let rec matches_pat scrutinee_orig p =
                let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig  in
                let uu____23515 = FStar_Syntax_Util.head_and_args scrutinee1
                   in
                match uu____23515 with
                | (head1,args) ->
                    (match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_var bv ->
                         FStar_Util.Inl [(bv, scrutinee_orig)]
                     | FStar_Syntax_Syntax.Pat_wild bv ->
                         FStar_Util.Inl [(bv, scrutinee_orig)]
                     | FStar_Syntax_Syntax.Pat_dot_term uu____23602 ->
                         FStar_Util.Inl []
                     | FStar_Syntax_Syntax.Pat_constant s ->
                         (match scrutinee1.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_constant s' when
                              FStar_Const.eq_const s s' -> FStar_Util.Inl []
                          | uu____23641 ->
                              let uu____23642 =
                                let uu____23643 = is_cons head1  in
                                Prims.op_Negation uu____23643  in
                              FStar_Util.Inr uu____23642)
                     | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                         let uu____23668 =
                           let uu____23669 = FStar_Syntax_Util.un_uinst head1
                              in
                           uu____23669.FStar_Syntax_Syntax.n  in
                         (match uu____23668 with
                          | FStar_Syntax_Syntax.Tm_fvar fv' when
                              FStar_Syntax_Syntax.fv_eq fv fv' ->
                              matches_args [] args arg_pats
                          | uu____23687 ->
                              let uu____23688 =
                                let uu____23689 = is_cons head1  in
                                Prims.op_Negation uu____23689  in
                              FStar_Util.Inr uu____23688))
              
              and matches_args out a p =
                match (a, p) with
                | ([],[]) -> FStar_Util.Inl out
                | ((t2,uu____23758)::rest_a,(p1,uu____23761)::rest_p) ->
                    let uu____23805 = matches_pat t2 p1  in
                    (match uu____23805 with
                     | FStar_Util.Inl s ->
                         matches_args (FStar_List.append out s) rest_a rest_p
                     | m -> m)
                | uu____23854 -> FStar_Util.Inr false
               in
              let rec matches scrutinee1 p =
                match p with
                | [] -> norm_and_rebuild_match ()
                | (p1,wopt,b)::rest ->
                    let uu____23964 = matches_pat scrutinee1 p1  in
                    (match uu____23964 with
                     | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                     | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                     | FStar_Util.Inl s ->
                         let uu____24000 =
                           log cfg1
                             (fun uu____24004  ->
                                let uu____24005 =
                                  FStar_Syntax_Print.pat_to_string p1  in
                                let uu____24006 =
                                  let uu____24007 =
                                    FStar_List.map
                                      (fun uu____24017  ->
                                         match uu____24017 with
                                         | (uu____24022,t2) ->
                                             FStar_Syntax_Print.term_to_string
                                               t2) s
                                     in
                                  FStar_All.pipe_right uu____24007
                                    (FStar_String.concat "; ")
                                   in
                                FStar_Util.print2
                                  "Matches pattern %s with subst = %s\n"
                                  uu____24005 uu____24006)
                            in
                         let env0 = env1  in
                         let env2 =
                           FStar_List.fold_left
                             (fun env2  ->
                                fun uu____24054  ->
                                  match uu____24054 with
                                  | (bv,t2) ->
                                      let uu____24077 =
                                        let uu____24084 =
                                          let uu____24087 =
                                            FStar_Syntax_Syntax.mk_binder bv
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____24087
                                           in
                                        let uu____24088 =
                                          let uu____24089 =
                                            let uu____24120 =
                                              FStar_Util.mk_ref
                                                (FStar_Pervasives_Native.Some
                                                   ([], t2))
                                               in
                                            ([], t2, uu____24120, false)  in
                                          Clos uu____24089  in
                                        (uu____24084, uu____24088)  in
                                      uu____24077 :: env2) env1 s
                            in
                         let uu____24237 = guard_when_clause wopt b rest  in
                         norm cfg1 env2 stack1 uu____24237)
                 in
              if (cfg1.steps).iota
              then matches scrutinee branches
              else norm_and_rebuild_match ()

let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____24264 =
      let uu____24267 = FStar_ST.op_Bang plugins  in p :: uu____24267  in
    FStar_ST.op_Colon_Equals plugins uu____24264  in
  let retrieve uu____24375 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24452  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_24493  ->
                  match uu___92_24493 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24497 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24503 -> d  in
        let uu____24506 = to_fsteps s  in
        let uu____24507 =
          let uu____24508 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24509 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24510 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24511 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24512 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24508;
            primop = uu____24509;
            b380 = uu____24510;
            norm_delayed = uu____24511;
            print_normalized = uu____24512
          }  in
        let uu____24513 =
          let uu____24516 =
            let uu____24519 = retrieve_plugins ()  in
            FStar_List.append uu____24519 psteps  in
          add_steps built_in_primitive_steps uu____24516  in
        let uu____24522 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24524 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24524)
           in
        {
          steps = uu____24506;
          tcenv = e;
          debug = uu____24507;
          delta_level = d1;
          primitive_steps = uu____24513;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24522
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
      fun t  -> let uu____24606 = config s e  in norm_comp uu____24606 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24623 = config [] env  in norm_universe uu____24623 [] u
  
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
        let uu____24647 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24647  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24654 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___192_24673 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___192_24673.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___192_24673.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24680 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24680
          then
            let ct1 =
              let uu____24682 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24682 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24689 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24689
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___193_24693 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___193_24693.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___193_24693.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___193_24693.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___194_24695 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___194_24695.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___194_24695.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___194_24695.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___194_24695.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___195_24696 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___195_24696.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_24696.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24698 -> c
  
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
        let uu____24716 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24716  in
      let uu____24723 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24723
      then
        let uu____24724 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24724 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24730  ->
                 let uu____24731 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24731)
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
            let uu____24751 =
              let uu____24752 =
                let uu____24757 =
                  let uu____24758 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24758
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24757)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24752
               in
            t
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24773 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24773 [] c
        with
        | e ->
            let uu____24785 =
              let uu____24786 =
                let uu____24791 =
                  let uu____24792 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24792
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24791)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24786
               in
            c
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
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
                   let uu____24837 =
                     let uu____24838 =
                       let uu____24845 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24845)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24838  in
                   mk uu____24837 t01.FStar_Syntax_Syntax.pos
               | uu____24850 -> t2)
          | uu____24851 -> t2  in
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
             DoNotUnfoldPureLets;
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
        let uu____24915 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____24915 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____24944 ->
                 let uu____24951 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____24951 with
                  | (actuals,uu____24961,uu____24962) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____24976 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____24976 with
                         | (binders,args) ->
                             let uu____24993 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____24993
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
      | uu____25005 ->
          let uu____25006 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25006 with
           | (head1,args) ->
               let uu____25043 =
                 let uu____25044 = FStar_Syntax_Subst.compress head1  in
                 uu____25044.FStar_Syntax_Syntax.n  in
               (match uu____25043 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25047,thead) ->
                    let uu____25073 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25073 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25115 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_25123 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_25123.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_25123.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_25123.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_25123.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_25123.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_25123.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_25123.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_25123.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_25123.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_25123.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_25123.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_25123.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_25123.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_25123.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_25123.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_25123.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_25123.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_25123.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___200_25123.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___200_25123.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___200_25123.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_25123.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_25123.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___200_25123.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___200_25123.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___200_25123.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___200_25123.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___200_25123.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___200_25123.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___200_25123.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___200_25123.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___200_25123.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___200_25123.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___200_25123.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25115 with
                            | (uu____25124,ty,uu____25126) ->
                                eta_expand_with_type env t ty))
                | uu____25127 ->
                    let uu____25128 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_25136 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_25136.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_25136.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_25136.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_25136.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_25136.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_25136.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_25136.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_25136.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_25136.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_25136.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_25136.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_25136.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_25136.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_25136.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_25136.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_25136.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_25136.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_25136.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___201_25136.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___201_25136.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___201_25136.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_25136.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_25136.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___201_25136.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___201_25136.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___201_25136.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___201_25136.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___201_25136.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___201_25136.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___201_25136.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___201_25136.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___201_25136.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___201_25136.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___201_25136.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25128 with
                     | (uu____25137,ty,uu____25139) ->
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
      let uu___202_25212 = x  in
      let uu____25213 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___202_25212.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___202_25212.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25213
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25216 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25241 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25242 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25243 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25244 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25251 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25252 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25253 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___203_25283 = rc  in
          let uu____25284 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25291 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___203_25283.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25284;
            FStar_Syntax_Syntax.residual_flags = uu____25291
          }  in
        let uu____25294 =
          let uu____25295 =
            let uu____25312 = elim_delayed_subst_binders bs  in
            let uu____25319 = elim_delayed_subst_term t2  in
            let uu____25320 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25312, uu____25319, uu____25320)  in
          FStar_Syntax_Syntax.Tm_abs uu____25295  in
        mk1 uu____25294
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25349 =
          let uu____25350 =
            let uu____25363 = elim_delayed_subst_binders bs  in
            let uu____25370 = elim_delayed_subst_comp c  in
            (uu____25363, uu____25370)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25350  in
        mk1 uu____25349
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25383 =
          let uu____25384 =
            let uu____25391 = elim_bv bv  in
            let uu____25392 = elim_delayed_subst_term phi  in
            (uu____25391, uu____25392)  in
          FStar_Syntax_Syntax.Tm_refine uu____25384  in
        mk1 uu____25383
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25415 =
          let uu____25416 =
            let uu____25431 = elim_delayed_subst_term t2  in
            let uu____25432 = elim_delayed_subst_args args  in
            (uu____25431, uu____25432)  in
          FStar_Syntax_Syntax.Tm_app uu____25416  in
        mk1 uu____25415
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___204_25498 = p  in
              let uu____25499 =
                let uu____25500 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25500  in
              {
                FStar_Syntax_Syntax.v = uu____25499;
                FStar_Syntax_Syntax.p =
                  (uu___204_25498.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___205_25502 = p  in
              let uu____25503 =
                let uu____25504 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25504  in
              {
                FStar_Syntax_Syntax.v = uu____25503;
                FStar_Syntax_Syntax.p =
                  (uu___205_25502.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___206_25511 = p  in
              let uu____25512 =
                let uu____25513 =
                  let uu____25520 = elim_bv x  in
                  let uu____25521 = elim_delayed_subst_term t0  in
                  (uu____25520, uu____25521)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25513  in
              {
                FStar_Syntax_Syntax.v = uu____25512;
                FStar_Syntax_Syntax.p =
                  (uu___206_25511.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___207_25540 = p  in
              let uu____25541 =
                let uu____25542 =
                  let uu____25555 =
                    FStar_List.map
                      (fun uu____25578  ->
                         match uu____25578 with
                         | (x,b) ->
                             let uu____25591 = elim_pat x  in
                             (uu____25591, b)) pats
                     in
                  (fv, uu____25555)  in
                FStar_Syntax_Syntax.Pat_cons uu____25542  in
              {
                FStar_Syntax_Syntax.v = uu____25541;
                FStar_Syntax_Syntax.p =
                  (uu___207_25540.FStar_Syntax_Syntax.p)
              }
          | uu____25604 -> p  in
        let elim_branch uu____25628 =
          match uu____25628 with
          | (pat,wopt,t3) ->
              let uu____25654 = elim_pat pat  in
              let uu____25657 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25660 = elim_delayed_subst_term t3  in
              (uu____25654, uu____25657, uu____25660)
           in
        let uu____25665 =
          let uu____25666 =
            let uu____25689 = elim_delayed_subst_term t2  in
            let uu____25690 = FStar_List.map elim_branch branches  in
            (uu____25689, uu____25690)  in
          FStar_Syntax_Syntax.Tm_match uu____25666  in
        mk1 uu____25665
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25801 =
          match uu____25801 with
          | (tc,topt) ->
              let uu____25836 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25846 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25846
                | FStar_Util.Inr c ->
                    let uu____25848 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25848
                 in
              let uu____25849 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25836, uu____25849)
           in
        let uu____25858 =
          let uu____25859 =
            let uu____25886 = elim_delayed_subst_term t2  in
            let uu____25887 = elim_ascription a  in
            (uu____25886, uu____25887, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____25859  in
        mk1 uu____25858
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___208_25934 = lb  in
          let uu____25935 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____25938 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___208_25934.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___208_25934.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____25935;
            FStar_Syntax_Syntax.lbeff =
              (uu___208_25934.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____25938;
            FStar_Syntax_Syntax.lbattrs =
              (uu___208_25934.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___208_25934.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____25941 =
          let uu____25942 =
            let uu____25955 =
              let uu____25962 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____25962)  in
            let uu____25971 = elim_delayed_subst_term t2  in
            (uu____25955, uu____25971)  in
          FStar_Syntax_Syntax.Tm_let uu____25942  in
        mk1 uu____25941
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26004 =
          let uu____26005 =
            let uu____26022 = elim_delayed_subst_term t2  in
            (uv, uu____26022)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26005  in
        mk1 uu____26004
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26040 =
          let uu____26041 =
            let uu____26048 = elim_delayed_subst_term tm  in
            (uu____26048, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26041  in
        mk1 uu____26040
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26055 =
          let uu____26056 =
            let uu____26063 = elim_delayed_subst_term t2  in
            let uu____26064 = elim_delayed_subst_meta md  in
            (uu____26063, uu____26064)  in
          FStar_Syntax_Syntax.Tm_meta uu____26056  in
        mk1 uu____26055

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_26071  ->
         match uu___93_26071 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26075 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26075
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
        let uu____26098 =
          let uu____26099 =
            let uu____26108 = elim_delayed_subst_term t  in
            (uu____26108, uopt)  in
          FStar_Syntax_Syntax.Total uu____26099  in
        mk1 uu____26098
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26121 =
          let uu____26122 =
            let uu____26131 = elim_delayed_subst_term t  in
            (uu____26131, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26122  in
        mk1 uu____26121
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___209_26136 = ct  in
          let uu____26137 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26140 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26149 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___209_26136.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___209_26136.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26137;
            FStar_Syntax_Syntax.effect_args = uu____26140;
            FStar_Syntax_Syntax.flags = uu____26149
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_26152  ->
    match uu___94_26152 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26164 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26164
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26197 =
          let uu____26204 = elim_delayed_subst_term t  in (m, uu____26204)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26197
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26212 =
          let uu____26221 = elim_delayed_subst_term t  in
          (m1, m2, uu____26221)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26212
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26244  ->
         match uu____26244 with
         | (t,q) ->
             let uu____26255 = elim_delayed_subst_term t  in (uu____26255, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26275  ->
         match uu____26275 with
         | (x,q) ->
             let uu____26286 =
               let uu___210_26287 = x  in
               let uu____26288 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___210_26287.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___210_26287.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26288
               }  in
             (uu____26286, q)) bs

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
            | (uu____26372,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26378,FStar_Util.Inl t) ->
                let uu____26384 =
                  let uu____26391 =
                    let uu____26392 =
                      let uu____26405 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26405)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26392  in
                  FStar_Syntax_Syntax.mk uu____26391  in
                uu____26384 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26409 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26409 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26437 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26492 ->
                    let uu____26493 =
                      let uu____26502 =
                        let uu____26503 = FStar_Syntax_Subst.compress t4  in
                        uu____26503.FStar_Syntax_Syntax.n  in
                      (uu____26502, tc)  in
                    (match uu____26493 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26528) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26565) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26604,FStar_Util.Inl uu____26605) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26628 -> failwith "Impossible")
                 in
              (match uu____26437 with
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
          let uu____26741 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26741 with
          | (univ_names1,binders1,tc) ->
              let uu____26799 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26799)
  
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
          let uu____26842 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26842 with
          | (univ_names1,binders1,tc) ->
              let uu____26902 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____26902)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____26939 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____26939 with
           | (univ_names1,binders1,typ1) ->
               let uu___211_26967 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_26967.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_26967.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_26967.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_26967.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___212_26988 = s  in
          let uu____26989 =
            let uu____26990 =
              let uu____26999 = FStar_List.map (elim_uvars env) sigs  in
              (uu____26999, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____26990  in
          {
            FStar_Syntax_Syntax.sigel = uu____26989;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_26988.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_26988.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_26988.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_26988.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27016 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27016 with
           | (univ_names1,uu____27034,typ1) ->
               let uu___213_27048 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_27048.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_27048.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_27048.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_27048.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27054 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27054 with
           | (univ_names1,uu____27072,typ1) ->
               let uu___214_27086 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_27086.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_27086.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_27086.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_27086.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27120 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27120 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27145 =
                            let uu____27146 =
                              let uu____27147 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27147  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27146
                             in
                          elim_delayed_subst_term uu____27145  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___215_27150 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___215_27150.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_27150.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___215_27150.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___215_27150.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___216_27151 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___216_27151.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_27151.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_27151.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_27151.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___217_27163 = s  in
          let uu____27164 =
            let uu____27165 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27165  in
          {
            FStar_Syntax_Syntax.sigel = uu____27164;
            FStar_Syntax_Syntax.sigrng =
              (uu___217_27163.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_27163.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_27163.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_27163.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27169 = elim_uvars_aux_t env us [] t  in
          (match uu____27169 with
           | (us1,uu____27187,t1) ->
               let uu___218_27201 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_27201.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_27201.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_27201.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_27201.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27202 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27204 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27204 with
           | (univs1,binders,signature) ->
               let uu____27232 =
                 let uu____27241 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27241 with
                 | (univs_opening,univs2) ->
                     let uu____27268 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27268)
                  in
               (match uu____27232 with
                | (univs_opening,univs_closing) ->
                    let uu____27285 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27291 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27292 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27291, uu____27292)  in
                    (match uu____27285 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27316 =
                           match uu____27316 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27334 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27334 with
                                | (us1,t1) ->
                                    let uu____27345 =
                                      let uu____27350 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27357 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27350, uu____27357)  in
                                    (match uu____27345 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27370 =
                                           let uu____27375 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27384 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27375, uu____27384)  in
                                         (match uu____27370 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27400 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27400
                                                 in
                                              let uu____27401 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27401 with
                                               | (uu____27422,uu____27423,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27438 =
                                                       let uu____27439 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27439
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27438
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27446 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27446 with
                           | (uu____27459,uu____27460,t1) -> t1  in
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
                             | uu____27522 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27541 =
                               let uu____27542 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27542.FStar_Syntax_Syntax.n  in
                             match uu____27541 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27601 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27632 =
                               let uu____27633 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27633.FStar_Syntax_Syntax.n  in
                             match uu____27632 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27654) ->
                                 let uu____27675 = destruct_action_body body
                                    in
                                 (match uu____27675 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27720 ->
                                 let uu____27721 = destruct_action_body t  in
                                 (match uu____27721 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27770 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27770 with
                           | (action_univs,t) ->
                               let uu____27779 = destruct_action_typ_templ t
                                  in
                               (match uu____27779 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___219_27820 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___219_27820.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___219_27820.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___220_27822 = ed  in
                           let uu____27823 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27824 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27825 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27826 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27827 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27828 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27829 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27833 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27836 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___220_27822.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___220_27822.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27823;
                             FStar_Syntax_Syntax.bind_wp = uu____27824;
                             FStar_Syntax_Syntax.if_then_else = uu____27825;
                             FStar_Syntax_Syntax.ite_wp = uu____27826;
                             FStar_Syntax_Syntax.stronger = uu____27827;
                             FStar_Syntax_Syntax.close_wp = uu____27828;
                             FStar_Syntax_Syntax.assert_p = uu____27829;
                             FStar_Syntax_Syntax.assume_p = uu____27830;
                             FStar_Syntax_Syntax.null_wp = uu____27831;
                             FStar_Syntax_Syntax.trivial = uu____27832;
                             FStar_Syntax_Syntax.repr = uu____27833;
                             FStar_Syntax_Syntax.return_repr = uu____27834;
                             FStar_Syntax_Syntax.bind_repr = uu____27835;
                             FStar_Syntax_Syntax.actions = uu____27836;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___220_27822.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___221_27839 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___221_27839.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___221_27839.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___221_27839.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___221_27839.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_27858 =
            match uu___95_27858 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____27885 = elim_uvars_aux_t env us [] t  in
                (match uu____27885 with
                 | (us1,uu____27909,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___222_27928 = sub_eff  in
            let uu____27929 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27932 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___222_27928.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___222_27928.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27929;
              FStar_Syntax_Syntax.lift = uu____27932
            }  in
          let uu___223_27935 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___223_27935.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_27935.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_27935.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_27935.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27945 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27945 with
           | (univ_names1,binders1,comp1) ->
               let uu___224_27979 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_27979.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_27979.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_27979.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_27979.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27990 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27991 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  