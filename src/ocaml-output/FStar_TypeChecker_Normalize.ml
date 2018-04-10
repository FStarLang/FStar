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
      let add_opt x uu___78_1402 =
        match uu___78_1402 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1422 = fs  in
          {
            beta = true;
            iota = (uu___96_1422.iota);
            zeta = (uu___96_1422.zeta);
            weak = (uu___96_1422.weak);
            hnf = (uu___96_1422.hnf);
            primops = (uu___96_1422.primops);
            do_not_unfold_pure_lets = (uu___96_1422.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1422.unfold_until);
            unfold_only = (uu___96_1422.unfold_only);
            unfold_fully = (uu___96_1422.unfold_fully);
            unfold_attr = (uu___96_1422.unfold_attr);
            unfold_tac = (uu___96_1422.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1422.pure_subterms_within_computations);
            simplify = (uu___96_1422.simplify);
            erase_universes = (uu___96_1422.erase_universes);
            allow_unbound_universes = (uu___96_1422.allow_unbound_universes);
            reify_ = (uu___96_1422.reify_);
            compress_uvars = (uu___96_1422.compress_uvars);
            no_full_norm = (uu___96_1422.no_full_norm);
            check_no_uvars = (uu___96_1422.check_no_uvars);
            unmeta = (uu___96_1422.unmeta);
            unascribe = (uu___96_1422.unascribe);
            in_full_norm_request = (uu___96_1422.in_full_norm_request)
          }
      | Iota  ->
          let uu___97_1423 = fs  in
          {
            beta = (uu___97_1423.beta);
            iota = true;
            zeta = (uu___97_1423.zeta);
            weak = (uu___97_1423.weak);
            hnf = (uu___97_1423.hnf);
            primops = (uu___97_1423.primops);
            do_not_unfold_pure_lets = (uu___97_1423.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1423.unfold_until);
            unfold_only = (uu___97_1423.unfold_only);
            unfold_fully = (uu___97_1423.unfold_fully);
            unfold_attr = (uu___97_1423.unfold_attr);
            unfold_tac = (uu___97_1423.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1423.pure_subterms_within_computations);
            simplify = (uu___97_1423.simplify);
            erase_universes = (uu___97_1423.erase_universes);
            allow_unbound_universes = (uu___97_1423.allow_unbound_universes);
            reify_ = (uu___97_1423.reify_);
            compress_uvars = (uu___97_1423.compress_uvars);
            no_full_norm = (uu___97_1423.no_full_norm);
            check_no_uvars = (uu___97_1423.check_no_uvars);
            unmeta = (uu___97_1423.unmeta);
            unascribe = (uu___97_1423.unascribe);
            in_full_norm_request = (uu___97_1423.in_full_norm_request)
          }
      | Zeta  ->
          let uu___98_1424 = fs  in
          {
            beta = (uu___98_1424.beta);
            iota = (uu___98_1424.iota);
            zeta = true;
            weak = (uu___98_1424.weak);
            hnf = (uu___98_1424.hnf);
            primops = (uu___98_1424.primops);
            do_not_unfold_pure_lets = (uu___98_1424.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1424.unfold_until);
            unfold_only = (uu___98_1424.unfold_only);
            unfold_fully = (uu___98_1424.unfold_fully);
            unfold_attr = (uu___98_1424.unfold_attr);
            unfold_tac = (uu___98_1424.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1424.pure_subterms_within_computations);
            simplify = (uu___98_1424.simplify);
            erase_universes = (uu___98_1424.erase_universes);
            allow_unbound_universes = (uu___98_1424.allow_unbound_universes);
            reify_ = (uu___98_1424.reify_);
            compress_uvars = (uu___98_1424.compress_uvars);
            no_full_norm = (uu___98_1424.no_full_norm);
            check_no_uvars = (uu___98_1424.check_no_uvars);
            unmeta = (uu___98_1424.unmeta);
            unascribe = (uu___98_1424.unascribe);
            in_full_norm_request = (uu___98_1424.in_full_norm_request)
          }
      | Exclude (Beta ) ->
          let uu___99_1425 = fs  in
          {
            beta = false;
            iota = (uu___99_1425.iota);
            zeta = (uu___99_1425.zeta);
            weak = (uu___99_1425.weak);
            hnf = (uu___99_1425.hnf);
            primops = (uu___99_1425.primops);
            do_not_unfold_pure_lets = (uu___99_1425.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1425.unfold_until);
            unfold_only = (uu___99_1425.unfold_only);
            unfold_fully = (uu___99_1425.unfold_fully);
            unfold_attr = (uu___99_1425.unfold_attr);
            unfold_tac = (uu___99_1425.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1425.pure_subterms_within_computations);
            simplify = (uu___99_1425.simplify);
            erase_universes = (uu___99_1425.erase_universes);
            allow_unbound_universes = (uu___99_1425.allow_unbound_universes);
            reify_ = (uu___99_1425.reify_);
            compress_uvars = (uu___99_1425.compress_uvars);
            no_full_norm = (uu___99_1425.no_full_norm);
            check_no_uvars = (uu___99_1425.check_no_uvars);
            unmeta = (uu___99_1425.unmeta);
            unascribe = (uu___99_1425.unascribe);
            in_full_norm_request = (uu___99_1425.in_full_norm_request)
          }
      | Exclude (Iota ) ->
          let uu___100_1426 = fs  in
          {
            beta = (uu___100_1426.beta);
            iota = false;
            zeta = (uu___100_1426.zeta);
            weak = (uu___100_1426.weak);
            hnf = (uu___100_1426.hnf);
            primops = (uu___100_1426.primops);
            do_not_unfold_pure_lets = (uu___100_1426.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1426.unfold_until);
            unfold_only = (uu___100_1426.unfold_only);
            unfold_fully = (uu___100_1426.unfold_fully);
            unfold_attr = (uu___100_1426.unfold_attr);
            unfold_tac = (uu___100_1426.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1426.pure_subterms_within_computations);
            simplify = (uu___100_1426.simplify);
            erase_universes = (uu___100_1426.erase_universes);
            allow_unbound_universes = (uu___100_1426.allow_unbound_universes);
            reify_ = (uu___100_1426.reify_);
            compress_uvars = (uu___100_1426.compress_uvars);
            no_full_norm = (uu___100_1426.no_full_norm);
            check_no_uvars = (uu___100_1426.check_no_uvars);
            unmeta = (uu___100_1426.unmeta);
            unascribe = (uu___100_1426.unascribe);
            in_full_norm_request = (uu___100_1426.in_full_norm_request)
          }
      | Exclude (Zeta ) ->
          let uu___101_1427 = fs  in
          {
            beta = (uu___101_1427.beta);
            iota = (uu___101_1427.iota);
            zeta = false;
            weak = (uu___101_1427.weak);
            hnf = (uu___101_1427.hnf);
            primops = (uu___101_1427.primops);
            do_not_unfold_pure_lets = (uu___101_1427.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1427.unfold_until);
            unfold_only = (uu___101_1427.unfold_only);
            unfold_fully = (uu___101_1427.unfold_fully);
            unfold_attr = (uu___101_1427.unfold_attr);
            unfold_tac = (uu___101_1427.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1427.pure_subterms_within_computations);
            simplify = (uu___101_1427.simplify);
            erase_universes = (uu___101_1427.erase_universes);
            allow_unbound_universes = (uu___101_1427.allow_unbound_universes);
            reify_ = (uu___101_1427.reify_);
            compress_uvars = (uu___101_1427.compress_uvars);
            no_full_norm = (uu___101_1427.no_full_norm);
            check_no_uvars = (uu___101_1427.check_no_uvars);
            unmeta = (uu___101_1427.unmeta);
            unascribe = (uu___101_1427.unascribe);
            in_full_norm_request = (uu___101_1427.in_full_norm_request)
          }
      | Exclude uu____1428 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1429 = fs  in
          {
            beta = (uu___102_1429.beta);
            iota = (uu___102_1429.iota);
            zeta = (uu___102_1429.zeta);
            weak = true;
            hnf = (uu___102_1429.hnf);
            primops = (uu___102_1429.primops);
            do_not_unfold_pure_lets = (uu___102_1429.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1429.unfold_until);
            unfold_only = (uu___102_1429.unfold_only);
            unfold_fully = (uu___102_1429.unfold_fully);
            unfold_attr = (uu___102_1429.unfold_attr);
            unfold_tac = (uu___102_1429.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1429.pure_subterms_within_computations);
            simplify = (uu___102_1429.simplify);
            erase_universes = (uu___102_1429.erase_universes);
            allow_unbound_universes = (uu___102_1429.allow_unbound_universes);
            reify_ = (uu___102_1429.reify_);
            compress_uvars = (uu___102_1429.compress_uvars);
            no_full_norm = (uu___102_1429.no_full_norm);
            check_no_uvars = (uu___102_1429.check_no_uvars);
            unmeta = (uu___102_1429.unmeta);
            unascribe = (uu___102_1429.unascribe);
            in_full_norm_request = (uu___102_1429.in_full_norm_request)
          }
      | HNF  ->
          let uu___103_1430 = fs  in
          {
            beta = (uu___103_1430.beta);
            iota = (uu___103_1430.iota);
            zeta = (uu___103_1430.zeta);
            weak = (uu___103_1430.weak);
            hnf = true;
            primops = (uu___103_1430.primops);
            do_not_unfold_pure_lets = (uu___103_1430.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1430.unfold_until);
            unfold_only = (uu___103_1430.unfold_only);
            unfold_fully = (uu___103_1430.unfold_fully);
            unfold_attr = (uu___103_1430.unfold_attr);
            unfold_tac = (uu___103_1430.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1430.pure_subterms_within_computations);
            simplify = (uu___103_1430.simplify);
            erase_universes = (uu___103_1430.erase_universes);
            allow_unbound_universes = (uu___103_1430.allow_unbound_universes);
            reify_ = (uu___103_1430.reify_);
            compress_uvars = (uu___103_1430.compress_uvars);
            no_full_norm = (uu___103_1430.no_full_norm);
            check_no_uvars = (uu___103_1430.check_no_uvars);
            unmeta = (uu___103_1430.unmeta);
            unascribe = (uu___103_1430.unascribe);
            in_full_norm_request = (uu___103_1430.in_full_norm_request)
          }
      | Primops  ->
          let uu___104_1431 = fs  in
          {
            beta = (uu___104_1431.beta);
            iota = (uu___104_1431.iota);
            zeta = (uu___104_1431.zeta);
            weak = (uu___104_1431.weak);
            hnf = (uu___104_1431.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1431.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1431.unfold_until);
            unfold_only = (uu___104_1431.unfold_only);
            unfold_fully = (uu___104_1431.unfold_fully);
            unfold_attr = (uu___104_1431.unfold_attr);
            unfold_tac = (uu___104_1431.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1431.pure_subterms_within_computations);
            simplify = (uu___104_1431.simplify);
            erase_universes = (uu___104_1431.erase_universes);
            allow_unbound_universes = (uu___104_1431.allow_unbound_universes);
            reify_ = (uu___104_1431.reify_);
            compress_uvars = (uu___104_1431.compress_uvars);
            no_full_norm = (uu___104_1431.no_full_norm);
            check_no_uvars = (uu___104_1431.check_no_uvars);
            unmeta = (uu___104_1431.unmeta);
            unascribe = (uu___104_1431.unascribe);
            in_full_norm_request = (uu___104_1431.in_full_norm_request)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1432 = fs  in
          {
            beta = (uu___105_1432.beta);
            iota = (uu___105_1432.iota);
            zeta = (uu___105_1432.zeta);
            weak = (uu___105_1432.weak);
            hnf = (uu___105_1432.hnf);
            primops = (uu___105_1432.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1432.unfold_until);
            unfold_only = (uu___105_1432.unfold_only);
            unfold_fully = (uu___105_1432.unfold_fully);
            unfold_attr = (uu___105_1432.unfold_attr);
            unfold_tac = (uu___105_1432.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1432.pure_subterms_within_computations);
            simplify = (uu___105_1432.simplify);
            erase_universes = (uu___105_1432.erase_universes);
            allow_unbound_universes = (uu___105_1432.allow_unbound_universes);
            reify_ = (uu___105_1432.reify_);
            compress_uvars = (uu___105_1432.compress_uvars);
            no_full_norm = (uu___105_1432.no_full_norm);
            check_no_uvars = (uu___105_1432.check_no_uvars);
            unmeta = (uu___105_1432.unmeta);
            unascribe = (uu___105_1432.unascribe);
            in_full_norm_request = (uu___105_1432.in_full_norm_request)
          }
      | UnfoldUntil d ->
          let uu___106_1434 = fs  in
          {
            beta = (uu___106_1434.beta);
            iota = (uu___106_1434.iota);
            zeta = (uu___106_1434.zeta);
            weak = (uu___106_1434.weak);
            hnf = (uu___106_1434.hnf);
            primops = (uu___106_1434.primops);
            do_not_unfold_pure_lets = (uu___106_1434.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1434.unfold_only);
            unfold_fully = (uu___106_1434.unfold_fully);
            unfold_attr = (uu___106_1434.unfold_attr);
            unfold_tac = (uu___106_1434.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1434.pure_subterms_within_computations);
            simplify = (uu___106_1434.simplify);
            erase_universes = (uu___106_1434.erase_universes);
            allow_unbound_universes = (uu___106_1434.allow_unbound_universes);
            reify_ = (uu___106_1434.reify_);
            compress_uvars = (uu___106_1434.compress_uvars);
            no_full_norm = (uu___106_1434.no_full_norm);
            check_no_uvars = (uu___106_1434.check_no_uvars);
            unmeta = (uu___106_1434.unmeta);
            unascribe = (uu___106_1434.unascribe);
            in_full_norm_request = (uu___106_1434.in_full_norm_request)
          }
      | UnfoldOnly lids ->
          let uu___107_1438 = fs  in
          {
            beta = (uu___107_1438.beta);
            iota = (uu___107_1438.iota);
            zeta = (uu___107_1438.zeta);
            weak = (uu___107_1438.weak);
            hnf = (uu___107_1438.hnf);
            primops = (uu___107_1438.primops);
            do_not_unfold_pure_lets = (uu___107_1438.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1438.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1438.unfold_fully);
            unfold_attr = (uu___107_1438.unfold_attr);
            unfold_tac = (uu___107_1438.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1438.pure_subterms_within_computations);
            simplify = (uu___107_1438.simplify);
            erase_universes = (uu___107_1438.erase_universes);
            allow_unbound_universes = (uu___107_1438.allow_unbound_universes);
            reify_ = (uu___107_1438.reify_);
            compress_uvars = (uu___107_1438.compress_uvars);
            no_full_norm = (uu___107_1438.no_full_norm);
            check_no_uvars = (uu___107_1438.check_no_uvars);
            unmeta = (uu___107_1438.unmeta);
            unascribe = (uu___107_1438.unascribe);
            in_full_norm_request = (uu___107_1438.in_full_norm_request)
          }
      | UnfoldFully lids ->
          let uu___108_1444 = fs  in
          {
            beta = (uu___108_1444.beta);
            iota = (uu___108_1444.iota);
            zeta = (uu___108_1444.zeta);
            weak = (uu___108_1444.weak);
            hnf = (uu___108_1444.hnf);
            primops = (uu___108_1444.primops);
            do_not_unfold_pure_lets = (uu___108_1444.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1444.unfold_until);
            unfold_only = (uu___108_1444.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1444.unfold_attr);
            unfold_tac = (uu___108_1444.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1444.pure_subterms_within_computations);
            simplify = (uu___108_1444.simplify);
            erase_universes = (uu___108_1444.erase_universes);
            allow_unbound_universes = (uu___108_1444.allow_unbound_universes);
            reify_ = (uu___108_1444.reify_);
            compress_uvars = (uu___108_1444.compress_uvars);
            no_full_norm = (uu___108_1444.no_full_norm);
            check_no_uvars = (uu___108_1444.check_no_uvars);
            unmeta = (uu___108_1444.unmeta);
            unascribe = (uu___108_1444.unascribe);
            in_full_norm_request = (uu___108_1444.in_full_norm_request)
          }
      | UnfoldAttr attr ->
          let uu___109_1448 = fs  in
          {
            beta = (uu___109_1448.beta);
            iota = (uu___109_1448.iota);
            zeta = (uu___109_1448.zeta);
            weak = (uu___109_1448.weak);
            hnf = (uu___109_1448.hnf);
            primops = (uu___109_1448.primops);
            do_not_unfold_pure_lets = (uu___109_1448.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1448.unfold_until);
            unfold_only = (uu___109_1448.unfold_only);
            unfold_fully = (uu___109_1448.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1448.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1448.pure_subterms_within_computations);
            simplify = (uu___109_1448.simplify);
            erase_universes = (uu___109_1448.erase_universes);
            allow_unbound_universes = (uu___109_1448.allow_unbound_universes);
            reify_ = (uu___109_1448.reify_);
            compress_uvars = (uu___109_1448.compress_uvars);
            no_full_norm = (uu___109_1448.no_full_norm);
            check_no_uvars = (uu___109_1448.check_no_uvars);
            unmeta = (uu___109_1448.unmeta);
            unascribe = (uu___109_1448.unascribe);
            in_full_norm_request = (uu___109_1448.in_full_norm_request)
          }
      | UnfoldTac  ->
          let uu___110_1449 = fs  in
          {
            beta = (uu___110_1449.beta);
            iota = (uu___110_1449.iota);
            zeta = (uu___110_1449.zeta);
            weak = (uu___110_1449.weak);
            hnf = (uu___110_1449.hnf);
            primops = (uu___110_1449.primops);
            do_not_unfold_pure_lets = (uu___110_1449.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1449.unfold_until);
            unfold_only = (uu___110_1449.unfold_only);
            unfold_fully = (uu___110_1449.unfold_fully);
            unfold_attr = (uu___110_1449.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1449.pure_subterms_within_computations);
            simplify = (uu___110_1449.simplify);
            erase_universes = (uu___110_1449.erase_universes);
            allow_unbound_universes = (uu___110_1449.allow_unbound_universes);
            reify_ = (uu___110_1449.reify_);
            compress_uvars = (uu___110_1449.compress_uvars);
            no_full_norm = (uu___110_1449.no_full_norm);
            check_no_uvars = (uu___110_1449.check_no_uvars);
            unmeta = (uu___110_1449.unmeta);
            unascribe = (uu___110_1449.unascribe);
            in_full_norm_request = (uu___110_1449.in_full_norm_request)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1450 = fs  in
          {
            beta = (uu___111_1450.beta);
            iota = (uu___111_1450.iota);
            zeta = (uu___111_1450.zeta);
            weak = (uu___111_1450.weak);
            hnf = (uu___111_1450.hnf);
            primops = (uu___111_1450.primops);
            do_not_unfold_pure_lets = (uu___111_1450.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1450.unfold_until);
            unfold_only = (uu___111_1450.unfold_only);
            unfold_fully = (uu___111_1450.unfold_fully);
            unfold_attr = (uu___111_1450.unfold_attr);
            unfold_tac = (uu___111_1450.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1450.simplify);
            erase_universes = (uu___111_1450.erase_universes);
            allow_unbound_universes = (uu___111_1450.allow_unbound_universes);
            reify_ = (uu___111_1450.reify_);
            compress_uvars = (uu___111_1450.compress_uvars);
            no_full_norm = (uu___111_1450.no_full_norm);
            check_no_uvars = (uu___111_1450.check_no_uvars);
            unmeta = (uu___111_1450.unmeta);
            unascribe = (uu___111_1450.unascribe);
            in_full_norm_request = (uu___111_1450.in_full_norm_request)
          }
      | Simplify  ->
          let uu___112_1451 = fs  in
          {
            beta = (uu___112_1451.beta);
            iota = (uu___112_1451.iota);
            zeta = (uu___112_1451.zeta);
            weak = (uu___112_1451.weak);
            hnf = (uu___112_1451.hnf);
            primops = (uu___112_1451.primops);
            do_not_unfold_pure_lets = (uu___112_1451.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1451.unfold_until);
            unfold_only = (uu___112_1451.unfold_only);
            unfold_fully = (uu___112_1451.unfold_fully);
            unfold_attr = (uu___112_1451.unfold_attr);
            unfold_tac = (uu___112_1451.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1451.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1451.erase_universes);
            allow_unbound_universes = (uu___112_1451.allow_unbound_universes);
            reify_ = (uu___112_1451.reify_);
            compress_uvars = (uu___112_1451.compress_uvars);
            no_full_norm = (uu___112_1451.no_full_norm);
            check_no_uvars = (uu___112_1451.check_no_uvars);
            unmeta = (uu___112_1451.unmeta);
            unascribe = (uu___112_1451.unascribe);
            in_full_norm_request = (uu___112_1451.in_full_norm_request)
          }
      | EraseUniverses  ->
          let uu___113_1452 = fs  in
          {
            beta = (uu___113_1452.beta);
            iota = (uu___113_1452.iota);
            zeta = (uu___113_1452.zeta);
            weak = (uu___113_1452.weak);
            hnf = (uu___113_1452.hnf);
            primops = (uu___113_1452.primops);
            do_not_unfold_pure_lets = (uu___113_1452.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1452.unfold_until);
            unfold_only = (uu___113_1452.unfold_only);
            unfold_fully = (uu___113_1452.unfold_fully);
            unfold_attr = (uu___113_1452.unfold_attr);
            unfold_tac = (uu___113_1452.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1452.pure_subterms_within_computations);
            simplify = (uu___113_1452.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1452.allow_unbound_universes);
            reify_ = (uu___113_1452.reify_);
            compress_uvars = (uu___113_1452.compress_uvars);
            no_full_norm = (uu___113_1452.no_full_norm);
            check_no_uvars = (uu___113_1452.check_no_uvars);
            unmeta = (uu___113_1452.unmeta);
            unascribe = (uu___113_1452.unascribe);
            in_full_norm_request = (uu___113_1452.in_full_norm_request)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1453 = fs  in
          {
            beta = (uu___114_1453.beta);
            iota = (uu___114_1453.iota);
            zeta = (uu___114_1453.zeta);
            weak = (uu___114_1453.weak);
            hnf = (uu___114_1453.hnf);
            primops = (uu___114_1453.primops);
            do_not_unfold_pure_lets = (uu___114_1453.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1453.unfold_until);
            unfold_only = (uu___114_1453.unfold_only);
            unfold_fully = (uu___114_1453.unfold_fully);
            unfold_attr = (uu___114_1453.unfold_attr);
            unfold_tac = (uu___114_1453.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1453.pure_subterms_within_computations);
            simplify = (uu___114_1453.simplify);
            erase_universes = (uu___114_1453.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1453.reify_);
            compress_uvars = (uu___114_1453.compress_uvars);
            no_full_norm = (uu___114_1453.no_full_norm);
            check_no_uvars = (uu___114_1453.check_no_uvars);
            unmeta = (uu___114_1453.unmeta);
            unascribe = (uu___114_1453.unascribe);
            in_full_norm_request = (uu___114_1453.in_full_norm_request)
          }
      | Reify  ->
          let uu___115_1454 = fs  in
          {
            beta = (uu___115_1454.beta);
            iota = (uu___115_1454.iota);
            zeta = (uu___115_1454.zeta);
            weak = (uu___115_1454.weak);
            hnf = (uu___115_1454.hnf);
            primops = (uu___115_1454.primops);
            do_not_unfold_pure_lets = (uu___115_1454.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1454.unfold_until);
            unfold_only = (uu___115_1454.unfold_only);
            unfold_fully = (uu___115_1454.unfold_fully);
            unfold_attr = (uu___115_1454.unfold_attr);
            unfold_tac = (uu___115_1454.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1454.pure_subterms_within_computations);
            simplify = (uu___115_1454.simplify);
            erase_universes = (uu___115_1454.erase_universes);
            allow_unbound_universes = (uu___115_1454.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1454.compress_uvars);
            no_full_norm = (uu___115_1454.no_full_norm);
            check_no_uvars = (uu___115_1454.check_no_uvars);
            unmeta = (uu___115_1454.unmeta);
            unascribe = (uu___115_1454.unascribe);
            in_full_norm_request = (uu___115_1454.in_full_norm_request)
          }
      | CompressUvars  ->
          let uu___116_1455 = fs  in
          {
            beta = (uu___116_1455.beta);
            iota = (uu___116_1455.iota);
            zeta = (uu___116_1455.zeta);
            weak = (uu___116_1455.weak);
            hnf = (uu___116_1455.hnf);
            primops = (uu___116_1455.primops);
            do_not_unfold_pure_lets = (uu___116_1455.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1455.unfold_until);
            unfold_only = (uu___116_1455.unfold_only);
            unfold_fully = (uu___116_1455.unfold_fully);
            unfold_attr = (uu___116_1455.unfold_attr);
            unfold_tac = (uu___116_1455.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1455.pure_subterms_within_computations);
            simplify = (uu___116_1455.simplify);
            erase_universes = (uu___116_1455.erase_universes);
            allow_unbound_universes = (uu___116_1455.allow_unbound_universes);
            reify_ = (uu___116_1455.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1455.no_full_norm);
            check_no_uvars = (uu___116_1455.check_no_uvars);
            unmeta = (uu___116_1455.unmeta);
            unascribe = (uu___116_1455.unascribe);
            in_full_norm_request = (uu___116_1455.in_full_norm_request)
          }
      | NoFullNorm  ->
          let uu___117_1456 = fs  in
          {
            beta = (uu___117_1456.beta);
            iota = (uu___117_1456.iota);
            zeta = (uu___117_1456.zeta);
            weak = (uu___117_1456.weak);
            hnf = (uu___117_1456.hnf);
            primops = (uu___117_1456.primops);
            do_not_unfold_pure_lets = (uu___117_1456.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1456.unfold_until);
            unfold_only = (uu___117_1456.unfold_only);
            unfold_fully = (uu___117_1456.unfold_fully);
            unfold_attr = (uu___117_1456.unfold_attr);
            unfold_tac = (uu___117_1456.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1456.pure_subterms_within_computations);
            simplify = (uu___117_1456.simplify);
            erase_universes = (uu___117_1456.erase_universes);
            allow_unbound_universes = (uu___117_1456.allow_unbound_universes);
            reify_ = (uu___117_1456.reify_);
            compress_uvars = (uu___117_1456.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1456.check_no_uvars);
            unmeta = (uu___117_1456.unmeta);
            unascribe = (uu___117_1456.unascribe);
            in_full_norm_request = (uu___117_1456.in_full_norm_request)
          }
      | CheckNoUvars  ->
          let uu___118_1457 = fs  in
          {
            beta = (uu___118_1457.beta);
            iota = (uu___118_1457.iota);
            zeta = (uu___118_1457.zeta);
            weak = (uu___118_1457.weak);
            hnf = (uu___118_1457.hnf);
            primops = (uu___118_1457.primops);
            do_not_unfold_pure_lets = (uu___118_1457.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1457.unfold_until);
            unfold_only = (uu___118_1457.unfold_only);
            unfold_fully = (uu___118_1457.unfold_fully);
            unfold_attr = (uu___118_1457.unfold_attr);
            unfold_tac = (uu___118_1457.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1457.pure_subterms_within_computations);
            simplify = (uu___118_1457.simplify);
            erase_universes = (uu___118_1457.erase_universes);
            allow_unbound_universes = (uu___118_1457.allow_unbound_universes);
            reify_ = (uu___118_1457.reify_);
            compress_uvars = (uu___118_1457.compress_uvars);
            no_full_norm = (uu___118_1457.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1457.unmeta);
            unascribe = (uu___118_1457.unascribe);
            in_full_norm_request = (uu___118_1457.in_full_norm_request)
          }
      | Unmeta  ->
          let uu___119_1458 = fs  in
          {
            beta = (uu___119_1458.beta);
            iota = (uu___119_1458.iota);
            zeta = (uu___119_1458.zeta);
            weak = (uu___119_1458.weak);
            hnf = (uu___119_1458.hnf);
            primops = (uu___119_1458.primops);
            do_not_unfold_pure_lets = (uu___119_1458.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1458.unfold_until);
            unfold_only = (uu___119_1458.unfold_only);
            unfold_fully = (uu___119_1458.unfold_fully);
            unfold_attr = (uu___119_1458.unfold_attr);
            unfold_tac = (uu___119_1458.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1458.pure_subterms_within_computations);
            simplify = (uu___119_1458.simplify);
            erase_universes = (uu___119_1458.erase_universes);
            allow_unbound_universes = (uu___119_1458.allow_unbound_universes);
            reify_ = (uu___119_1458.reify_);
            compress_uvars = (uu___119_1458.compress_uvars);
            no_full_norm = (uu___119_1458.no_full_norm);
            check_no_uvars = (uu___119_1458.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1458.unascribe);
            in_full_norm_request = (uu___119_1458.in_full_norm_request)
          }
      | Unascribe  ->
          let uu___120_1459 = fs  in
          {
            beta = (uu___120_1459.beta);
            iota = (uu___120_1459.iota);
            zeta = (uu___120_1459.zeta);
            weak = (uu___120_1459.weak);
            hnf = (uu___120_1459.hnf);
            primops = (uu___120_1459.primops);
            do_not_unfold_pure_lets = (uu___120_1459.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1459.unfold_until);
            unfold_only = (uu___120_1459.unfold_only);
            unfold_fully = (uu___120_1459.unfold_fully);
            unfold_attr = (uu___120_1459.unfold_attr);
            unfold_tac = (uu___120_1459.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1459.pure_subterms_within_computations);
            simplify = (uu___120_1459.simplify);
            erase_universes = (uu___120_1459.erase_universes);
            allow_unbound_universes = (uu___120_1459.allow_unbound_universes);
            reify_ = (uu___120_1459.reify_);
            compress_uvars = (uu___120_1459.compress_uvars);
            no_full_norm = (uu___120_1459.no_full_norm);
            check_no_uvars = (uu___120_1459.check_no_uvars);
            unmeta = (uu___120_1459.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1459.in_full_norm_request)
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1509  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1788 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1892 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1905 -> false
  
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
             let uu____2203 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2203 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2217 = FStar_Util.psmap_empty ()  in add_steps uu____2217 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2232 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2232
  
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
    match projectee with | Arg _0 -> true | uu____2380 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2418 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2456 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2529 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2579 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2637 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2681 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2721 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2759 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2777 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2804 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2804 with | (hd1,uu____2818) -> hd1
  
let mk :
  'Auu____2841 .
    'Auu____2841 ->
      FStar_Range.range -> 'Auu____2841 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2904 = FStar_ST.op_Bang r  in
          match uu____2904 with
          | FStar_Pervasives_Native.Some uu____2956 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3032 =
      FStar_List.map
        (fun uu____3046  ->
           match uu____3046 with
           | (bopt,c) ->
               let uu____3059 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3061 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3059 uu____3061) env
       in
    FStar_All.pipe_right uu____3032 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_3064  ->
    match uu___79_3064 with
    | Clos (env,t,uu____3067,uu____3068) ->
        let uu____3113 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3120 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3113 uu____3120
    | Univ uu____3121 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_3126  ->
    match uu___80_3126 with
    | Arg (c,uu____3128,uu____3129) ->
        let uu____3130 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3130
    | MemoLazy uu____3131 -> "MemoLazy"
    | Abs (uu____3138,bs,uu____3140,uu____3141,uu____3142) ->
        let uu____3147 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3147
    | UnivArgs uu____3152 -> "UnivArgs"
    | Match uu____3159 -> "Match"
    | App (uu____3168,t,uu____3170,uu____3171) ->
        let uu____3172 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3172
    | Meta (uu____3173,m,uu____3175) -> "Meta"
    | Let uu____3176 -> "Let"
    | Cfg uu____3185 -> "Cfg"
    | Debug (t,uu____3187) ->
        let uu____3188 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3188
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3198 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3198 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3239 . 'Auu____3239 Prims.list -> Prims.bool =
  fun uu___81_3246  ->
    match uu___81_3246 with | [] -> true | uu____3249 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3281 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3281
      with
      | uu____3300 ->
          let uu____3301 =
            let uu____3302 = FStar_Syntax_Print.db_to_string x  in
            let uu____3303 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3302
              uu____3303
             in
          failwith uu____3301
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3311 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3311
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3315 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3315
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3319 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3319
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
          let uu____3352 =
            FStar_List.fold_left
              (fun uu____3378  ->
                 fun u1  ->
                   match uu____3378 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3403 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3403 with
                        | (k_u,n1) ->
                            let uu____3418 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3418
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3352 with
          | (uu____3436,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3462 =
                   let uu____3463 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3463  in
                 match uu____3462 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3481 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3489 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3495 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3504 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3513 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3520 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3520 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3537 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3537 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3545 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3553 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3553 with
                                  | (uu____3558,m) -> n1 <= m))
                           in
                        if uu____3545 then rest1 else us1
                    | uu____3563 -> us1)
               | uu____3568 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3572 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3572
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3576 = aux u  in
           match uu____3576 with
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
          let uu____3717 =
            log cfg
              (fun uu____3722  ->
                 let uu____3723 = FStar_Syntax_Print.tag_of_term t  in
                 let uu____3724 = env_to_string env  in
                 let uu____3725 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                   uu____3723 uu____3724 uu____3725)
             in
          match env with
          | [] when
              FStar_All.pipe_left Prims.op_Negation
                (cfg.steps).compress_uvars
              -> rebuild_closure cfg env stack t
          | uu____3734 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____3737 ->
                   let uu____3762 = FStar_Syntax_Subst.compress t  in
                   inline_closure_env cfg env stack uu____3762
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_constant uu____3763 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_name uu____3764 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_lazy uu____3765 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_fvar uu____3766 ->
                   rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_uvar uu____3767 ->
                   if (cfg.steps).check_no_uvars
                   then
                     let t1 = FStar_Syntax_Subst.compress t  in
                     (match t1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_uvar uu____3789 ->
                          let uu____3806 =
                            let uu____3807 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____3808 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.format2
                              "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                              uu____3807 uu____3808
                             in
                          failwith uu____3806
                      | uu____3811 -> inline_closure_env cfg env stack t1)
                   else rebuild_closure cfg env stack t
               | FStar_Syntax_Syntax.Tm_type u ->
                   let t1 =
                     let uu____3817 =
                       let uu____3818 = norm_universe cfg env u  in
                       FStar_Syntax_Syntax.Tm_type uu____3818  in
                     mk uu____3817 t.FStar_Syntax_Syntax.pos  in
                   rebuild_closure cfg env stack t1
               | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                   let t1 =
                     let uu____3826 =
                       FStar_List.map (norm_universe cfg env) us  in
                     FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3826  in
                   rebuild_closure cfg env stack t1
               | FStar_Syntax_Syntax.Tm_bvar x ->
                   let uu____3828 = lookup_bvar env x  in
                   (match uu____3828 with
                    | Univ uu____3831 ->
                        failwith
                          "Impossible: term variable is bound to a universe"
                    | Dummy  ->
                        let x1 =
                          let uu___125_3835 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___125_3835.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___125_3835.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              FStar_Syntax_Syntax.tun
                          }  in
                        let t1 =
                          mk (FStar_Syntax_Syntax.Tm_bvar x1)
                            t.FStar_Syntax_Syntax.pos
                           in
                        rebuild_closure cfg env stack t1
                    | Clos (env1,t0,uu____3841,uu____3842) ->
                        inline_closure_env cfg env1 stack t0)
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let stack1 =
                     FStar_All.pipe_right stack
                       (FStar_List.fold_right
                          (fun uu____3927  ->
                             fun stack1  ->
                               match uu____3927 with
                               | (a,aq) ->
                                   let uu____3939 =
                                     let uu____3940 =
                                       let uu____3947 =
                                         let uu____3948 =
                                           let uu____3979 =
                                             FStar_Util.mk_ref
                                               FStar_Pervasives_Native.None
                                              in
                                           (env, a, uu____3979, false)  in
                                         Clos uu____3948  in
                                       (uu____3947, aq,
                                         (t.FStar_Syntax_Syntax.pos))
                                        in
                                     Arg uu____3940  in
                                   uu____3939 :: stack1) args)
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
                   let uu____4173 = close_binders cfg env bs  in
                   (match uu____4173 with
                    | (bs1,env') ->
                        let c1 = close_comp cfg env' c  in
                        let t1 =
                          mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                            t.FStar_Syntax_Syntax.pos
                           in
                        rebuild_closure cfg env stack t1)
               | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                   let uu____4220 =
                     let uu____4231 =
                       let uu____4238 = FStar_Syntax_Syntax.mk_binder x  in
                       [uu____4238]  in
                     close_binders cfg env uu____4231  in
                   (match uu____4220 with
                    | (x1,env1) ->
                        let phi1 = non_tail_inline_closure_env cfg env1 phi
                           in
                        let t1 =
                          let uu____4261 =
                            let uu____4262 =
                              let uu____4269 =
                                let uu____4270 = FStar_List.hd x1  in
                                FStar_All.pipe_right uu____4270
                                  FStar_Pervasives_Native.fst
                                 in
                              (uu____4269, phi1)  in
                            FStar_Syntax_Syntax.Tm_refine uu____4262  in
                          mk uu____4261 t.FStar_Syntax_Syntax.pos  in
                        rebuild_closure cfg env1 stack t1)
               | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                   let annot1 =
                     match annot with
                     | FStar_Util.Inl t2 ->
                         let uu____4361 =
                           non_tail_inline_closure_env cfg env t2  in
                         FStar_Util.Inl uu____4361
                     | FStar_Util.Inr c ->
                         let uu____4375 = close_comp cfg env c  in
                         FStar_Util.Inr uu____4375
                      in
                   let tacopt1 =
                     FStar_Util.map_opt tacopt
                       (non_tail_inline_closure_env cfg env)
                      in
                   let t2 =
                     let uu____4394 =
                       let uu____4395 =
                         let uu____4422 =
                           non_tail_inline_closure_env cfg env t1  in
                         (uu____4422, (annot1, tacopt1), lopt)  in
                       FStar_Syntax_Syntax.Tm_ascribed uu____4395  in
                     mk uu____4394 t.FStar_Syntax_Syntax.pos  in
                   rebuild_closure cfg env stack t2
               | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                   let t1 =
                     match qi.FStar_Syntax_Syntax.qkind with
                     | FStar_Syntax_Syntax.Quote_dynamic  ->
                         let uu____4468 =
                           let uu____4469 =
                             let uu____4476 =
                               non_tail_inline_closure_env cfg env t'  in
                             (uu____4476, qi)  in
                           FStar_Syntax_Syntax.Tm_quoted uu____4469  in
                         mk uu____4468 t.FStar_Syntax_Syntax.pos
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
                       (fun env1  -> fun uu____4528  -> dummy :: env1) env
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
                   let uu____4549 =
                     let uu____4560 = FStar_Syntax_Syntax.is_top_level [lb]
                        in
                     if uu____4560
                     then ((lb.FStar_Syntax_Syntax.lbname), body)
                     else
                       (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                           in
                        let uu____4579 =
                          non_tail_inline_closure_env cfg (dummy :: env0)
                            body
                           in
                        ((FStar_Util.Inl
                            (let uu___126_4595 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___126_4595.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___126_4595.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = typ
                             })), uu____4579))
                      in
                   (match uu____4549 with
                    | (nm,body1) ->
                        let lb1 =
                          let uu___127_4613 = lb  in
                          {
                            FStar_Syntax_Syntax.lbname = nm;
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___127_4613.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp = typ;
                            FStar_Syntax_Syntax.lbeff =
                              (uu___127_4613.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef = def;
                            FStar_Syntax_Syntax.lbattrs =
                              (uu___127_4613.FStar_Syntax_Syntax.lbattrs);
                            FStar_Syntax_Syntax.lbpos =
                              (uu___127_4613.FStar_Syntax_Syntax.lbpos)
                          }  in
                        let t1 =
                          mk
                            (FStar_Syntax_Syntax.Tm_let
                               ((false, [lb1]), body1))
                            t.FStar_Syntax_Syntax.pos
                           in
                        rebuild_closure cfg env0 stack t1)
               | FStar_Syntax_Syntax.Tm_let ((uu____4627,lbs),body) ->
                   let norm_one_lb env1 lb =
                     let env_univs =
                       FStar_List.fold_right
                         (fun uu____4688  -> fun env2  -> dummy :: env2)
                         lb.FStar_Syntax_Syntax.lbunivs env1
                        in
                     let env2 =
                       let uu____4713 = FStar_Syntax_Syntax.is_top_level lbs
                          in
                       if uu____4713
                       then env_univs
                       else
                         FStar_List.fold_right
                           (fun uu____4733  -> fun env2  -> dummy :: env2)
                           lbs env_univs
                        in
                     let ty =
                       non_tail_inline_closure_env cfg env_univs
                         lb.FStar_Syntax_Syntax.lbtyp
                        in
                     let nm =
                       let uu____4757 = FStar_Syntax_Syntax.is_top_level lbs
                          in
                       if uu____4757
                       then lb.FStar_Syntax_Syntax.lbname
                       else
                         (let x =
                            FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                          FStar_Util.Inl
                            (let uu___128_4765 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___128_4765.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___128_4765.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }))
                        in
                     let uu___129_4766 = lb  in
                     let uu____4767 =
                       non_tail_inline_closure_env cfg env2
                         lb.FStar_Syntax_Syntax.lbdef
                        in
                     {
                       FStar_Syntax_Syntax.lbname = nm;
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___129_4766.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp = ty;
                       FStar_Syntax_Syntax.lbeff =
                         (uu___129_4766.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef = uu____4767;
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___129_4766.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___129_4766.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let lbs1 =
                     FStar_All.pipe_right lbs
                       (FStar_List.map (norm_one_lb env))
                      in
                   let body1 =
                     let body_env =
                       FStar_List.fold_right
                         (fun uu____4799  -> fun env1  -> dummy :: env1) lbs1
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
          let uu____4896 =
            log cfg
              (fun uu____4902  ->
                 let uu____4903 = FStar_Syntax_Print.tag_of_term t  in
                 let uu____4904 = env_to_string env  in
                 let uu____4905 = stack_to_string stack  in
                 let uu____4906 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.print4
                   "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                   uu____4903 uu____4904 uu____4905 uu____4906)
             in
          match stack with
          | [] -> t
          | (Arg (Clos (env_arg,tm,uu____4911,uu____4912),aq,r))::stack1 ->
              let stack2 = (App (env, t, aq, r)) :: stack1  in
              inline_closure_env cfg env_arg stack2 tm
          | (App (env1,head1,aq,r))::stack1 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r
                 in
              rebuild_closure cfg env1 stack1 t1
          | (Abs (env',bs,env'',lopt,r))::stack1 ->
              let uu____4987 = close_binders cfg env' bs  in
              (match uu____4987 with
               | (bs1,uu____5001) ->
                   let lopt1 = close_lcomp_opt cfg env'' lopt  in
                   let uu____5017 =
                     let uu___130_5018 = FStar_Syntax_Util.abs bs1 t lopt1
                        in
                     {
                       FStar_Syntax_Syntax.n =
                         (uu___130_5018.FStar_Syntax_Syntax.n);
                       FStar_Syntax_Syntax.pos = r;
                       FStar_Syntax_Syntax.vars =
                         (uu___130_5018.FStar_Syntax_Syntax.vars)
                     }  in
                   rebuild_closure cfg env stack1 uu____5017)
          | (Match (env1,branches,cfg1,r))::stack1 ->
              let close_one_branch env2 uu____5062 =
                match uu____5062 with
                | (pat,w_opt,tm) ->
                    let rec norm_pat env3 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____5135 ->
                          (p, env3)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____5156 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____5216  ->
                                    fun uu____5217  ->
                                      match (uu____5216, uu____5217) with
                                      | ((pats1,env4),(p1,b)) ->
                                          let uu____5308 = norm_pat env4 p1
                                             in
                                          (match uu____5308 with
                                           | (p2,env5) ->
                                               (((p2, b) :: pats1), env5)))
                                 ([], env3))
                             in
                          (match uu____5156 with
                           | (pats1,env4) ->
                               ((let uu___131_5390 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___131_5390.FStar_Syntax_Syntax.p)
                                 }), env4))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___132_5409 = x  in
                            let uu____5410 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___132_5409.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___132_5409.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5410
                            }  in
                          ((let uu___133_5424 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___133_5424.FStar_Syntax_Syntax.p)
                            }), (dummy :: env3))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___134_5435 = x  in
                            let uu____5436 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___134_5435.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___134_5435.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5436
                            }  in
                          ((let uu___135_5450 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___135_5450.FStar_Syntax_Syntax.p)
                            }), (dummy :: env3))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___136_5466 = x  in
                            let uu____5467 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___136_5466.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___136_5466.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5467
                            }  in
                          let t2 = non_tail_inline_closure_env cfg1 env3 t1
                             in
                          ((let uu___137_5476 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___137_5476.FStar_Syntax_Syntax.p)
                            }), env3)
                       in
                    let uu____5481 = norm_pat env2 pat  in
                    (match uu____5481 with
                     | (pat1,env3) ->
                         let w_opt1 =
                           match w_opt with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some w ->
                               let uu____5526 =
                                 non_tail_inline_closure_env cfg1 env3 w  in
                               FStar_Pervasives_Native.Some uu____5526
                            in
                         let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                            in
                         (pat1, w_opt1, tm1))
                 in
              let t1 =
                let uu____5545 =
                  let uu____5546 =
                    let uu____5569 =
                      FStar_All.pipe_right branches
                        (FStar_List.map (close_one_branch env1))
                       in
                    (t, uu____5569)  in
                  FStar_Syntax_Syntax.Tm_match uu____5546  in
                mk uu____5545 t.FStar_Syntax_Syntax.pos  in
              rebuild_closure cfg1 env1 stack1 t1
          | (Meta (env_m,m,r))::stack1 ->
              let m1 =
                match m with
                | FStar_Syntax_Syntax.Meta_pattern args ->
                    let uu____5664 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun args1  ->
                              FStar_All.pipe_right args1
                                (FStar_List.map
                                   (fun uu____5753  ->
                                      match uu____5753 with
                                      | (a,q) ->
                                          let uu____5772 =
                                            non_tail_inline_closure_env cfg
                                              env_m a
                                             in
                                          (uu____5772, q)))))
                       in
                    FStar_Syntax_Syntax.Meta_pattern uu____5664
                | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                    let uu____5783 =
                      let uu____5790 =
                        non_tail_inline_closure_env cfg env_m tbody  in
                      (m1, uu____5790)  in
                    FStar_Syntax_Syntax.Meta_monadic uu____5783
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                    let uu____5802 =
                      let uu____5811 =
                        non_tail_inline_closure_env cfg env_m tbody  in
                      (m1, m2, uu____5811)  in
                    FStar_Syntax_Syntax.Meta_monadic_lift uu____5802
                | uu____5816 -> m  in
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
              rebuild_closure cfg env stack1 t1
          | uu____5820 -> failwith "Impossible: unexpected stack element"

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
        let uu____5834 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5883  ->
                  fun uu____5884  ->
                    match (uu____5883, uu____5884) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_5954 = b  in
                          let uu____5955 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_5954.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_5954.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5955
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5834 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6048 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6061 = inline_closure_env cfg env [] t  in
                 let uu____6062 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6061 uu____6062
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6075 = inline_closure_env cfg env [] t  in
                 let uu____6076 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6075 uu____6076
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6122  ->
                           match uu____6122 with
                           | (a,q) ->
                               let uu____6135 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6135, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_6150  ->
                           match uu___82_6150 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6154 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6154
                           | f -> f))
                    in
                 let uu____6158 =
                   let uu___139_6159 = c1  in
                   let uu____6160 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6160;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_6159.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6158)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_6170  ->
            match uu___83_6170 with
            | FStar_Syntax_Syntax.DECREASES uu____6171 -> false
            | uu____6174 -> true))

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
                   (fun uu___84_6192  ->
                      match uu___84_6192 with
                      | FStar_Syntax_Syntax.DECREASES uu____6193 -> false
                      | uu____6196 -> true))
               in
            let rc1 =
              let uu___140_6198 = rc  in
              let uu____6199 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_6198.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6199;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6208 -> lopt

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
  let arg_as_list a e a =
    let uu____6312 =
      let uu____6320 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6320  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6312  in
  let arg_as_bounded_int uu____6345 =
    match uu____6345 with
    | (a,uu____6357) ->
        let uu____6364 =
          let uu____6365 = FStar_Syntax_Subst.compress a  in
          uu____6365.FStar_Syntax_Syntax.n  in
        (match uu____6364 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6375;
                FStar_Syntax_Syntax.vars = uu____6376;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6378;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6379;_},uu____6380)::[])
             when
             let uu____6419 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6419 "int_to_t" ->
             let uu____6420 =
               let uu____6425 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6425)  in
             FStar_Pervasives_Native.Some uu____6420
         | uu____6430 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6474 = f a  in FStar_Pervasives_Native.Some uu____6474
    | uu____6475 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6527 = f a0 a1  in FStar_Pervasives_Native.Some uu____6527
    | uu____6528 -> FStar_Pervasives_Native.None  in
  let unary_op a247 a248 a249 a250 a251 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6575 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a246  -> (Obj.magic (f res.psc_range)) a246)
                    uu____6575)) a247 a248 a249 a250 a251
     in
  let binary_op a254 a255 a256 a257 a258 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6629 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a252  ->
                       fun a253  -> (Obj.magic (f res.psc_range)) a252 a253)
                    uu____6629)) a254 a255 a256 a257 a258
     in
  let as_primitive_step is_strong uu____6658 =
    match uu____6658 with
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
    unary_op () (fun a259  -> (Obj.magic arg_as_int) a259)
      (fun a260  ->
         fun a261  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6715 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____6715)) a260 a261)
     in
  let binary_int_op f =
    binary_op () (fun a262  -> (Obj.magic arg_as_int) a262)
      (fun a263  ->
         fun a264  ->
           fun a265  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6748 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6748)) a263
               a264 a265)
     in
  let unary_bool_op f =
    unary_op () (fun a266  -> (Obj.magic arg_as_bool) a266)
      (fun a267  ->
         fun a268  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6774 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6774)) a267 a268)
     in
  let binary_bool_op f =
    binary_op () (fun a269  -> (Obj.magic arg_as_bool) a269)
      (fun a270  ->
         fun a271  ->
           fun a272  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6807 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6807)) a270
               a271 a272)
     in
  let binary_string_op f =
    binary_op () (fun a273  -> (Obj.magic arg_as_string) a273)
      (fun a274  ->
         fun a275  ->
           fun a276  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6840 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6840)) a274
               a275 a276)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6957 =
          let uu____6966 = as_a a  in
          let uu____6969 = as_b b  in (uu____6966, uu____6969)  in
        (match uu____6957 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6984 =
               let uu____6985 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6985  in
             FStar_Pervasives_Native.Some uu____6984
         | uu____6986 -> FStar_Pervasives_Native.None)
    | uu____6995 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7012 =
        let uu____7013 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7013  in
      mk uu____7012 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7024 =
      let uu____7027 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7027  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7024  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7064 =
      let uu____7065 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7065  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7064
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7085 = arg_as_string a1  in
        (match uu____7085 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7091 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____7091 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7104 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7104
              | uu____7105 -> FStar_Pervasives_Native.None)
         | uu____7110 -> FStar_Pervasives_Native.None)
    | uu____7113 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7125 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7125
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7158 =
          let uu____7179 = arg_as_string fn  in
          let uu____7182 = arg_as_int from_line  in
          let uu____7185 = arg_as_int from_col  in
          let uu____7188 = arg_as_int to_line  in
          let uu____7191 = arg_as_int to_col  in
          (uu____7179, uu____7182, uu____7185, uu____7188, uu____7191)  in
        (match uu____7158 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7222 =
                 let uu____7223 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7224 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7223 uu____7224  in
               let uu____7225 =
                 let uu____7226 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7227 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7226 uu____7227  in
               FStar_Range.mk_range fn1 uu____7222 uu____7225  in
             let uu____7228 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7228
         | uu____7229 -> FStar_Pervasives_Native.None)
    | uu____7250 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7280)::(a1,uu____7282)::(a2,uu____7284)::[] ->
        let uu____7321 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7321 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7334 -> FStar_Pervasives_Native.None)
    | uu____7335 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7364)::[] ->
        let uu____7373 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7373 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7379 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7379
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7380 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7406 =
      let uu____7423 =
        let uu____7440 =
          let uu____7457 =
            let uu____7474 =
              let uu____7491 =
                let uu____7508 =
                  let uu____7525 =
                    let uu____7542 =
                      let uu____7559 =
                        let uu____7576 =
                          let uu____7593 =
                            let uu____7610 =
                              let uu____7627 =
                                let uu____7644 =
                                  let uu____7661 =
                                    let uu____7678 =
                                      let uu____7695 =
                                        let uu____7712 =
                                          let uu____7729 =
                                            let uu____7746 =
                                              let uu____7763 =
                                                let uu____7778 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7778,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a277  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a277)
                                                     (fun a278  ->
                                                        fun a279  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a278 a279)))
                                                 in
                                              let uu____7787 =
                                                let uu____7804 =
                                                  let uu____7819 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7819,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a280  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a280)
                                                       (fun a281  ->
                                                          fun a282  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a281 a282)))
                                                   in
                                                let uu____7828 =
                                                  let uu____7845 =
                                                    let uu____7862 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7862,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7873 =
                                                    let uu____7892 =
                                                      let uu____7909 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7909,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7892]  in
                                                  uu____7845 :: uu____7873
                                                   in
                                                uu____7804 :: uu____7828  in
                                              uu____7763 :: uu____7787  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7746
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7729
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a283  ->
                                                (Obj.magic arg_as_string)
                                                  a283)
                                             (fun a284  ->
                                                fun a285  ->
                                                  fun a286  ->
                                                    (Obj.magic
                                                       string_compare') a284
                                                      a285 a286)))
                                          :: uu____7712
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a287  ->
                                              (Obj.magic arg_as_bool) a287)
                                           (fun a288  ->
                                              fun a289  ->
                                                (Obj.magic string_of_bool1)
                                                  a288 a289)))
                                        :: uu____7695
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a290  ->
                                            (Obj.magic arg_as_int) a290)
                                         (fun a291  ->
                                            fun a292  ->
                                              (Obj.magic string_of_int1) a291
                                                a292)))
                                      :: uu____7678
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a293  ->
                                          (Obj.magic arg_as_int) a293)
                                       (fun a294  ->
                                          (Obj.magic arg_as_char) a294)
                                       (fun a295  ->
                                          fun a296  ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a295 a296)
                                       (fun a297  ->
                                          fun a298  ->
                                            fun a299  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____8136 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____8136 y)) a297
                                                a298 a299)))
                                    :: uu____7661
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7644
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7627
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7610
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7593
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7576
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7559
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a300  -> (Obj.magic arg_as_int) a300)
                         (fun a301  ->
                            fun a302  ->
                              fun a303  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____8331 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____8331)) a301 a302 a303)))
                      :: uu____7542
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a304  -> (Obj.magic arg_as_int) a304)
                       (fun a305  ->
                          fun a306  ->
                            fun a307  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____8361 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____8361)) a305 a306 a307)))
                    :: uu____7525
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a308  -> (Obj.magic arg_as_int) a308)
                     (fun a309  ->
                        fun a310  ->
                          fun a311  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____8391 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____8391)) a309 a310 a311)))
                  :: uu____7508
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a312  -> (Obj.magic arg_as_int) a312)
                   (fun a313  ->
                      fun a314  ->
                        fun a315  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____8421 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____8421)) a313 a314 a315)))
                :: uu____7491
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7474
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7457
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7440
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7423
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7406
     in
  let weak_ops =
    let uu____8582 =
      let uu____8603 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8603, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8582]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8698 =
        let uu____8701 =
          let uu____8702 = FStar_Syntax_Syntax.as_arg c  in [uu____8702]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8701  in
      uu____8698 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8758 =
                let uu____8773 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____8773, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a316  -> (Obj.magic arg_as_bounded_int) a316)
                     (fun a317  ->
                        fun a318  ->
                          fun a319  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8791  ->
                                    fun uu____8792  ->
                                      match (uu____8791, uu____8792) with
                                      | ((int_to_t1,x),(uu____8811,y)) ->
                                          let uu____8821 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8821)) a317 a318 a319)))
                 in
              let uu____8822 =
                let uu____8839 =
                  let uu____8854 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____8854, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a320  -> (Obj.magic arg_as_bounded_int) a320)
                       (fun a321  ->
                          fun a322  ->
                            fun a323  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8872  ->
                                      fun uu____8873  ->
                                        match (uu____8872, uu____8873) with
                                        | ((int_to_t1,x),(uu____8892,y)) ->
                                            let uu____8902 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8902)) a321 a322 a323)))
                   in
                let uu____8903 =
                  let uu____8920 =
                    let uu____8935 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____8935, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a324  -> (Obj.magic arg_as_bounded_int) a324)
                         (fun a325  ->
                            fun a326  ->
                              fun a327  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8953  ->
                                        fun uu____8954  ->
                                          match (uu____8953, uu____8954) with
                                          | ((int_to_t1,x),(uu____8973,y)) ->
                                              let uu____8983 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8983)) a325 a326 a327)))
                     in
                  let uu____8984 =
                    let uu____9001 =
                      let uu____9016 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9016, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a328  -> (Obj.magic arg_as_bounded_int) a328)
                           (fun a329  ->
                              fun a330  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____9030  ->
                                        match uu____9030 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a329 a330)))
                       in
                    [uu____9001]  in
                  uu____8920 :: uu____8984  in
                uu____8839 :: uu____8903  in
              uu____8758 :: uu____8822))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9160 =
                let uu____9175 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9175, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a331  -> (Obj.magic arg_as_bounded_int) a331)
                     (fun a332  ->
                        fun a333  ->
                          fun a334  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____9193  ->
                                    fun uu____9194  ->
                                      match (uu____9193, uu____9194) with
                                      | ((int_to_t1,x),(uu____9213,y)) ->
                                          let uu____9223 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____9223)) a332 a333 a334)))
                 in
              let uu____9224 =
                let uu____9241 =
                  let uu____9256 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9256, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a335  -> (Obj.magic arg_as_bounded_int) a335)
                       (fun a336  ->
                          fun a337  ->
                            fun a338  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____9274  ->
                                      fun uu____9275  ->
                                        match (uu____9274, uu____9275) with
                                        | ((int_to_t1,x),(uu____9294,y)) ->
                                            let uu____9304 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____9304)) a336 a337 a338)))
                   in
                [uu____9241]  in
              uu____9160 :: uu____9224))
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
    | (_typ,uu____9432)::(a1,uu____9434)::(a2,uu____9436)::[] ->
        let uu____9473 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9473 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9479 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9479.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9479.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9483 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9483.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9483.FStar_Syntax_Syntax.vars)
                })
         | uu____9484 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9486)::uu____9487::(a1,uu____9489)::(a2,uu____9491)::[] ->
        let uu____9540 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9540 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9546 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9546.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9546.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9550 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9550.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9550.FStar_Syntax_Syntax.vars)
                })
         | uu____9551 -> FStar_Pervasives_Native.None)
    | uu____9552 -> failwith "Unexpected number of arguments"  in
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
    let uu____9606 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9606 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        let uu____9651 =
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
            (FStar_Errors.Warning_UnembedBinderKnot,
              "unembed_binder_knot is unset!")
           in
        FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____9658 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9658) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9720  ->
           fun subst1  ->
             match uu____9720 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9761,uu____9762)) ->
                      let uu____9821 = b  in
                      (match uu____9821 with
                       | (bv,uu____9829) ->
                           let uu____9830 =
                             let uu____9831 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____9831  in
                           if uu____9830
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____9836 = unembed_binder term1  in
                              match uu____9836 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____9843 =
                                      let uu___143_9844 = bv  in
                                      let uu____9845 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_9844.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_9844.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____9845
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____9843
                                     in
                                  let b_for_x =
                                    let uu____9849 =
                                      let uu____9856 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____9856)
                                       in
                                    FStar_Syntax_Syntax.NT uu____9849  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_9866  ->
                                         match uu___85_9866 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____9867,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9869;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9870;_})
                                             ->
                                             let uu____9875 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____9875
                                         | uu____9876 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____9877 -> subst1)) env []
  
let reduce_primops :
  'Auu____9900 'Auu____9901 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9900) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9901 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____9947 = FStar_Syntax_Util.head_and_args tm  in
             match uu____9947 with
             | (head1,args) ->
                 let uu____9984 =
                   let uu____9985 = FStar_Syntax_Util.un_uinst head1  in
                   uu____9985.FStar_Syntax_Syntax.n  in
                 (match uu____9984 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____9989 = find_prim_step cfg fv  in
                      (match uu____9989 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             let uu____10006 =
                               log_primops cfg
                                 (fun uu____10011  ->
                                    let uu____10012 =
                                      FStar_Syntax_Print.lid_to_string
                                        prim_step.name
                                       in
                                    let uu____10013 =
                                      FStar_Util.string_of_int l  in
                                    let uu____10020 =
                                      FStar_Util.string_of_int
                                        prim_step.arity
                                       in
                                    FStar_Util.print3
                                      "primop: found partially applied %s (%s/%s args)\n"
                                      uu____10012 uu____10013 uu____10020)
                                in
                             tm
                           else
                             (let uu____10022 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10022 with
                              | (args_1,args_2) ->
                                  let uu____10130 =
                                    log_primops cfg
                                      (fun uu____10133  ->
                                         let uu____10134 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: trying to reduce <%s>\n"
                                           uu____10134)
                                     in
                                  let psc =
                                    {
                                      psc_range =
                                        (head1.FStar_Syntax_Syntax.pos);
                                      psc_subst =
                                        (fun uu____10137  ->
                                           if
                                             prim_step.requires_binder_substitution
                                           then mk_psc_subst cfg env
                                           else [])
                                    }  in
                                  let uu____10139 =
                                    prim_step.interpretation psc args_1  in
                                  (match uu____10139 with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____10142 =
                                         log_primops cfg
                                           (fun uu____10145  ->
                                              let uu____10146 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10146)
                                          in
                                       tm
                                   | FStar_Pervasives_Native.Some reduced ->
                                       let uu____10148 =
                                         log_primops cfg
                                           (fun uu____10152  ->
                                              let uu____10153 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10154 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10153 uu____10154)
                                          in
                                       FStar_Syntax_Util.mk_app reduced
                                         args_2))
                       | FStar_Pervasives_Native.Some uu____10155 ->
                           let uu____10156 =
                             log_primops cfg
                               (fun uu____10159  ->
                                  let uu____10160 =
                                    FStar_Syntax_Print.term_to_string tm  in
                                  FStar_Util.print1
                                    "primop: not reducing <%s> since we're doing strong reduction\n"
                                    uu____10160)
                              in
                           tm
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      let uu____10161 =
                        log_primops cfg
                          (fun uu____10164  ->
                             let uu____10165 =
                               FStar_Syntax_Print.term_to_string tm  in
                             FStar_Util.print1 "primop: reducing <%s>\n"
                               uu____10165)
                         in
                      (match args with
                       | (a1,uu____10167)::[] ->
                           FStar_Syntax_Embeddings.embed
                             FStar_Syntax_Embeddings.e_range
                             tm.FStar_Syntax_Syntax.pos
                             a1.FStar_Syntax_Syntax.pos
                       | uu____10184 -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      let uu____10193 =
                        log_primops cfg
                          (fun uu____10196  ->
                             let uu____10197 =
                               FStar_Syntax_Print.term_to_string tm  in
                             FStar_Util.print1 "primop: reducing <%s>\n"
                               uu____10197)
                         in
                      (match args with
                       | (t,uu____10199)::(r,uu____10201)::[] ->
                           let uu____10228 =
                             FStar_Syntax_Embeddings.unembed
                               FStar_Syntax_Embeddings.e_range r
                              in
                           (match uu____10228 with
                            | FStar_Pervasives_Native.Some rng ->
                                let uu___144_10232 = t  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___144_10232.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___144_10232.FStar_Syntax_Syntax.vars)
                                }
                            | FStar_Pervasives_Native.None  -> tm)
                       | uu____10235 -> tm)
                  | uu____10244 -> tm))
  
let reduce_equality :
  'Auu____10255 'Auu____10256 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10255) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10256 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_10300 = cfg  in
         {
           steps =
             (let uu___146_10303 = default_steps  in
              {
                beta = (uu___146_10303.beta);
                iota = (uu___146_10303.iota);
                zeta = (uu___146_10303.zeta);
                weak = (uu___146_10303.weak);
                hnf = (uu___146_10303.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_10303.do_not_unfold_pure_lets);
                unfold_until = (uu___146_10303.unfold_until);
                unfold_only = (uu___146_10303.unfold_only);
                unfold_fully = (uu___146_10303.unfold_fully);
                unfold_attr = (uu___146_10303.unfold_attr);
                unfold_tac = (uu___146_10303.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_10303.pure_subterms_within_computations);
                simplify = (uu___146_10303.simplify);
                erase_universes = (uu___146_10303.erase_universes);
                allow_unbound_universes =
                  (uu___146_10303.allow_unbound_universes);
                reify_ = (uu___146_10303.reify_);
                compress_uvars = (uu___146_10303.compress_uvars);
                no_full_norm = (uu___146_10303.no_full_norm);
                check_no_uvars = (uu___146_10303.check_no_uvars);
                unmeta = (uu___146_10303.unmeta);
                unascribe = (uu___146_10303.unascribe);
                in_full_norm_request = (uu___146_10303.in_full_norm_request)
              });
           tcenv = (uu___145_10300.tcenv);
           debug = (uu___145_10300.debug);
           delta_level = (uu___145_10300.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_10300.strong);
           memoize_lazy = (uu___145_10300.memoize_lazy);
           normalize_pure_lets = (uu___145_10300.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10310 .
    FStar_Syntax_Syntax.term -> 'Auu____10310 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10325 =
        let uu____10332 =
          let uu____10333 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10333.FStar_Syntax_Syntax.n  in
        (uu____10332, args)  in
      match uu____10325 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10339::uu____10340::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10344::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10349::uu____10350::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10353 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_10366  ->
    match uu___86_10366 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10372 =
          let uu____10375 =
            let uu____10376 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10376  in
          [uu____10375]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10372
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10382 =
          let uu____10385 =
            let uu____10386 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10386  in
          [uu____10385]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10382
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10407 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10407) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10452 =
          let uu____10457 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10457 s  in
        match uu____10452 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10473 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10473
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10490::(tm,uu____10492)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10521)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10542)::uu____10543::(tm,uu____10545)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10584 =
            let uu____10589 = full_norm steps  in parse_steps uu____10589  in
          (match uu____10584 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10628 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_10647  ->
    match uu___87_10647 with
    | (App
        (uu____10650,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10651;
                       FStar_Syntax_Syntax.vars = uu____10652;_},uu____10653,uu____10654))::uu____10655
        -> true
    | uu____10662 -> false
  
let firstn :
  'Auu____10671 .
    Prims.int ->
      'Auu____10671 Prims.list ->
        ('Auu____10671 Prims.list,'Auu____10671 Prims.list)
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
          (uu____10713,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10714;
                         FStar_Syntax_Syntax.vars = uu____10715;_},uu____10716,uu____10717))::uu____10718
          -> (cfg.steps).reify_
      | uu____10725 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10747) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10757) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____10776  ->
                  match uu____10776 with
                  | (a,uu____10784) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10790 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____10815 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____10816 -> false
    | FStar_Syntax_Syntax.Tm_type uu____10833 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____10834 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____10835 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____10836 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____10837 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____10838 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____10845 -> false
    | FStar_Syntax_Syntax.Tm_let uu____10852 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____10865 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____10882 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____10895 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____10941  ->
                   match uu____10941 with
                   | (a,uu____10949) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right pats
             (FStar_Util.for_some
                (fun uu____11026  ->
                   match uu____11026 with
                   | (uu____11041,wopt,t2) ->
                       (match wopt with
                        | FStar_Pervasives_Native.None  -> false
                        | FStar_Pervasives_Native.Some t3 ->
                            maybe_weakly_reduced t3)
                         || (maybe_weakly_reduced t2))))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11069) ->
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
                     (fun uu____11191  ->
                        match uu____11191 with
                        | (a,uu____11199) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11204,uu____11205,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11211,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11217 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11224 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11225 -> false))
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            let uu____11516 =
              if (cfg.debug).norm_delayed
              then
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____11517 ->
                    let uu____11542 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "NORM delayed: %s\n" uu____11542
                | uu____11543 -> ()
              else ()  in
            FStar_Syntax_Subst.compress t  in
          let uu____11545 =
            log cfg
              (fun uu____11551  ->
                 let uu____11552 = FStar_Syntax_Print.tag_of_term t1  in
                 let uu____11553 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____11554 =
                   FStar_Util.string_of_int (FStar_List.length env)  in
                 let uu____11561 =
                   let uu____11562 =
                     let uu____11565 = firstn (Prims.parse_int "4") stack  in
                     FStar_All.pipe_left FStar_Pervasives_Native.fst
                       uu____11565
                      in
                   stack_to_string uu____11562  in
                 FStar_Util.print4
                   ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                   uu____11552 uu____11553 uu____11554 uu____11561)
             in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_constant uu____11588 ->
              rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_name uu____11589 ->
              rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_lazy uu____11590 ->
              rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_fvar
              { FStar_Syntax_Syntax.fv_name = uu____11591;
                FStar_Syntax_Syntax.fv_delta =
                  FStar_Syntax_Syntax.Delta_constant ;
                FStar_Syntax_Syntax.fv_qual = uu____11592;_}
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_fvar
              { FStar_Syntax_Syntax.fv_name = uu____11595;
                FStar_Syntax_Syntax.fv_delta = uu____11596;
                FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Data_ctor );_}
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_fvar
              { FStar_Syntax_Syntax.fv_name = uu____11597;
                FStar_Syntax_Syntax.fv_delta = uu____11598;
                FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Record_ctor uu____11599);_}
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_quoted uu____11606 ->
              let uu____11613 = closure_as_term cfg env t1  in
              rebuild cfg env stack uu____11613
          | FStar_Syntax_Syntax.Tm_app (hd1,args) when
              ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                 (is_norm_request hd1 args))
                &&
                (let uu____11643 =
                   FStar_Ident.lid_equals
                     (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                     FStar_Parser_Const.prims_lid
                    in
                 Prims.op_Negation uu____11643)
              ->
              let cfg' =
                let uu___147_11645 = cfg  in
                {
                  steps =
                    (let uu___148_11648 = cfg.steps  in
                     {
                       beta = (uu___148_11648.beta);
                       iota = (uu___148_11648.iota);
                       zeta = (uu___148_11648.zeta);
                       weak = (uu___148_11648.weak);
                       hnf = (uu___148_11648.hnf);
                       primops = (uu___148_11648.primops);
                       do_not_unfold_pure_lets = false;
                       unfold_until = (uu___148_11648.unfold_until);
                       unfold_only = FStar_Pervasives_Native.None;
                       unfold_fully = FStar_Pervasives_Native.None;
                       unfold_attr = (uu___148_11648.unfold_attr);
                       unfold_tac = (uu___148_11648.unfold_tac);
                       pure_subterms_within_computations =
                         (uu___148_11648.pure_subterms_within_computations);
                       simplify = (uu___148_11648.simplify);
                       erase_universes = (uu___148_11648.erase_universes);
                       allow_unbound_universes =
                         (uu___148_11648.allow_unbound_universes);
                       reify_ = (uu___148_11648.reify_);
                       compress_uvars = (uu___148_11648.compress_uvars);
                       no_full_norm = (uu___148_11648.no_full_norm);
                       check_no_uvars = (uu___148_11648.check_no_uvars);
                       unmeta = (uu___148_11648.unmeta);
                       unascribe = (uu___148_11648.unascribe);
                       in_full_norm_request =
                         (uu___148_11648.in_full_norm_request)
                     });
                  tcenv = (uu___147_11645.tcenv);
                  debug = (uu___147_11645.debug);
                  delta_level =
                    [FStar_TypeChecker_Env.Unfold
                       FStar_Syntax_Syntax.Delta_constant];
                  primitive_steps = (uu___147_11645.primitive_steps);
                  strong = (uu___147_11645.strong);
                  memoize_lazy = (uu___147_11645.memoize_lazy);
                  normalize_pure_lets = true
                }  in
              let uu____11653 = get_norm_request (norm cfg' env []) args  in
              (match uu____11653 with
               | FStar_Pervasives_Native.None  ->
                   let stack1 =
                     FStar_All.pipe_right stack
                       (FStar_List.fold_right
                          (fun uu____11684  ->
                             fun stack1  ->
                               match uu____11684 with
                               | (a,aq) ->
                                   let uu____11696 =
                                     let uu____11697 =
                                       let uu____11704 =
                                         let uu____11705 =
                                           let uu____11736 =
                                             FStar_Util.mk_ref
                                               FStar_Pervasives_Native.None
                                              in
                                           (env, a, uu____11736, false)  in
                                         Clos uu____11705  in
                                       (uu____11704, aq,
                                         (t1.FStar_Syntax_Syntax.pos))
                                        in
                                     Arg uu____11697  in
                                   uu____11696 :: stack1) args)
                      in
                   let uu____11817 =
                     log cfg
                       (fun uu____11820  ->
                          let uu____11821 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11821)
                      in
                   norm cfg env stack1 hd1
               | FStar_Pervasives_Native.Some (s,tm) ->
                   let delta_level =
                     let uu____11843 =
                       FStar_All.pipe_right s
                         (FStar_Util.for_some
                            (fun uu___88_11848  ->
                               match uu___88_11848 with
                               | UnfoldUntil uu____11849 -> true
                               | UnfoldOnly uu____11850 -> true
                               | UnfoldFully uu____11853 -> true
                               | uu____11856 -> false))
                        in
                     if uu____11843
                     then
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.Delta_constant]
                     else [FStar_TypeChecker_Env.NoDelta]  in
                   let cfg'1 =
                     let uu___149_11861 = cfg  in
                     let uu____11862 =
                       let uu___150_11863 = to_fsteps s  in
                       {
                         beta = (uu___150_11863.beta);
                         iota = (uu___150_11863.iota);
                         zeta = (uu___150_11863.zeta);
                         weak = (uu___150_11863.weak);
                         hnf = (uu___150_11863.hnf);
                         primops = (uu___150_11863.primops);
                         do_not_unfold_pure_lets =
                           (uu___150_11863.do_not_unfold_pure_lets);
                         unfold_until = (uu___150_11863.unfold_until);
                         unfold_only = (uu___150_11863.unfold_only);
                         unfold_fully = (uu___150_11863.unfold_fully);
                         unfold_attr = (uu___150_11863.unfold_attr);
                         unfold_tac = (uu___150_11863.unfold_tac);
                         pure_subterms_within_computations =
                           (uu___150_11863.pure_subterms_within_computations);
                         simplify = (uu___150_11863.simplify);
                         erase_universes = (uu___150_11863.erase_universes);
                         allow_unbound_universes =
                           (uu___150_11863.allow_unbound_universes);
                         reify_ = (uu___150_11863.reify_);
                         compress_uvars = (uu___150_11863.compress_uvars);
                         no_full_norm = (uu___150_11863.no_full_norm);
                         check_no_uvars = (uu___150_11863.check_no_uvars);
                         unmeta = (uu___150_11863.unmeta);
                         unascribe = (uu___150_11863.unascribe);
                         in_full_norm_request = true
                       }  in
                     {
                       steps = uu____11862;
                       tcenv = (uu___149_11861.tcenv);
                       debug = (uu___149_11861.debug);
                       delta_level;
                       primitive_steps = (uu___149_11861.primitive_steps);
                       strong = (uu___149_11861.strong);
                       memoize_lazy = (uu___149_11861.memoize_lazy);
                       normalize_pure_lets = true
                     }  in
                   let stack' =
                     let tail1 = (Cfg cfg) :: stack  in
                     if (cfg.debug).print_normalized
                     then
                       let uu____11872 =
                         let uu____11873 =
                           let uu____11878 = FStar_Util.now ()  in
                           (t1, uu____11878)  in
                         Debug uu____11873  in
                       uu____11872 :: tail1
                     else tail1  in
                   norm cfg'1 env stack' tm)
          | FStar_Syntax_Syntax.Tm_type u ->
              let u1 = norm_universe cfg env u  in
              let uu____11882 =
                mk (FStar_Syntax_Syntax.Tm_type u1)
                  t1.FStar_Syntax_Syntax.pos
                 in
              rebuild cfg env stack uu____11882
          | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
              if (cfg.steps).erase_universes
              then norm cfg env stack t'
              else
                (let us1 =
                   let uu____11891 =
                     let uu____11898 =
                       FStar_List.map (norm_universe cfg env) us  in
                     (uu____11898, (t1.FStar_Syntax_Syntax.pos))  in
                   UnivArgs uu____11891  in
                 let stack1 = us1 :: stack  in norm cfg env stack1 t')
          | FStar_Syntax_Syntax.Tm_fvar fv ->
              let qninfo =
                let uu____11908 = FStar_Syntax_Syntax.lid_of_fv fv  in
                FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____11908  in
              let uu____11909 = FStar_TypeChecker_Env.qninfo_is_action qninfo
                 in
              if uu____11909
              then
                let b = should_reify cfg stack  in
                let uu____11911 =
                  log cfg
                    (fun uu____11915  ->
                       let uu____11916 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11917 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____11916 uu____11917)
                   in
                (if b
                 then
                   let uu____11918 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____11918 t1 qninfo fv
                 else rebuild cfg env stack t1)
              else
                (let should_delta =
                   ((let uu____11926 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____11926) &&
                      (match qninfo with
                       | FStar_Pervasives_Native.Some
                           (FStar_Util.Inr
                            ({
                               FStar_Syntax_Syntax.sigel =
                                 FStar_Syntax_Syntax.Sig_let
                                 ((is_rec,uu____11939),uu____11940);
                               FStar_Syntax_Syntax.sigrng = uu____11941;
                               FStar_Syntax_Syntax.sigquals = qs;
                               FStar_Syntax_Syntax.sigmeta = uu____11943;
                               FStar_Syntax_Syntax.sigattrs = uu____11944;_},uu____11945),uu____11946)
                           ->
                           (Prims.op_Negation
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.HasMaskedEffect qs))
                             &&
                             ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                       | uu____12011 -> true))
                     &&
                     (FStar_All.pipe_right cfg.delta_level
                        (FStar_Util.for_some
                           (fun uu___89_12015  ->
                              match uu___89_12015 with
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
                         (let uu____12025 =
                            cases
                              (FStar_Util.for_some
                                 (FStar_Syntax_Util.attr_eq
                                    FStar_Syntax_Util.tac_opaque_attr)) false
                              attrs
                             in
                          Prims.op_Negation uu____12025))
                        &&
                        ((match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> true
                          | FStar_Pervasives_Native.Some lids ->
                              FStar_Util.for_some
                                (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                           ||
                           (match (attrs, ((cfg.steps).unfold_attr)) with
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.Some uu____12044) ->
                                false
                            | (FStar_Pervasives_Native.Some
                               ats,FStar_Pervasives_Native.Some ats') ->
                                FStar_Util.for_some
                                  (fun at  ->
                                     FStar_Util.for_some
                                       (FStar_Syntax_Util.attr_eq at) ats')
                                  ats
                            | (uu____12079,uu____12080) -> false)))
                    in
                 let uu____12097 =
                   match (cfg.steps).unfold_fully with
                   | FStar_Pervasives_Native.None  -> (should_delta1, false)
                   | FStar_Pervasives_Native.Some lids ->
                       let uu____12113 =
                         FStar_Util.for_some
                           (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                          in
                       if uu____12113 then (true, true) else (false, false)
                    in
                 match uu____12097 with
                 | (should_delta2,fully) ->
                     let uu____12121 =
                       log cfg
                         (fun uu____12126  ->
                            let uu____12127 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12128 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12129 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12127 uu____12128 uu____12129)
                        in
                     if should_delta2
                     then
                       let uu____12130 =
                         if fully
                         then
                           (((Cfg cfg) :: stack),
                             (let uu___151_12146 = cfg  in
                              {
                                steps =
                                  (let uu___152_12149 = cfg.steps  in
                                   {
                                     beta = (uu___152_12149.beta);
                                     iota = false;
                                     zeta = false;
                                     weak = false;
                                     hnf = false;
                                     primops = false;
                                     do_not_unfold_pure_lets =
                                       (uu___152_12149.do_not_unfold_pure_lets);
                                     unfold_until =
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.Delta_constant);
                                     unfold_only =
                                       FStar_Pervasives_Native.None;
                                     unfold_fully =
                                       FStar_Pervasives_Native.None;
                                     unfold_attr =
                                       (uu___152_12149.unfold_attr);
                                     unfold_tac = (uu___152_12149.unfold_tac);
                                     pure_subterms_within_computations =
                                       (uu___152_12149.pure_subterms_within_computations);
                                     simplify = false;
                                     erase_universes =
                                       (uu___152_12149.erase_universes);
                                     allow_unbound_universes =
                                       (uu___152_12149.allow_unbound_universes);
                                     reify_ = (uu___152_12149.reify_);
                                     compress_uvars =
                                       (uu___152_12149.compress_uvars);
                                     no_full_norm =
                                       (uu___152_12149.no_full_norm);
                                     check_no_uvars =
                                       (uu___152_12149.check_no_uvars);
                                     unmeta = (uu___152_12149.unmeta);
                                     unascribe = (uu___152_12149.unascribe);
                                     in_full_norm_request =
                                       (uu___152_12149.in_full_norm_request)
                                   });
                                tcenv = (uu___151_12146.tcenv);
                                debug = (uu___151_12146.debug);
                                delta_level = (uu___151_12146.delta_level);
                                primitive_steps =
                                  (uu___151_12146.primitive_steps);
                                strong = (uu___151_12146.strong);
                                memoize_lazy = (uu___151_12146.memoize_lazy);
                                normalize_pure_lets =
                                  (uu___151_12146.normalize_pure_lets)
                              }))
                         else (stack, cfg)  in
                       (match uu____12130 with
                        | (stack1,cfg1) ->
                            do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                     else rebuild cfg env stack t1)
          | FStar_Syntax_Syntax.Tm_bvar x ->
              let uu____12163 = lookup_bvar env x  in
              (match uu____12163 with
               | Univ uu____12164 ->
                   failwith
                     "Impossible: term variable is bound to a universe"
               | Dummy  -> failwith "Term variable not found"
               | Clos (env1,t0,r,fix) ->
                   if (Prims.op_Negation fix) || (cfg.steps).zeta
                   then
                     let uu____12213 = FStar_ST.op_Bang r  in
                     (match uu____12213 with
                      | FStar_Pervasives_Native.Some (env2,t') ->
                          let uu____12331 =
                            log cfg
                              (fun uu____12335  ->
                                 let uu____12336 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12337 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12336
                                   uu____12337)
                             in
                          let uu____12338 = maybe_weakly_reduced t'  in
                          if uu____12338
                          then
                            (match stack with
                             | [] when
                                 (cfg.steps).weak ||
                                   (cfg.steps).compress_uvars
                                 -> rebuild cfg env2 stack t'
                             | uu____12339 -> norm cfg env2 stack t')
                          else rebuild cfg env2 stack t'
                      | FStar_Pervasives_Native.None  ->
                          norm cfg env1 ((MemoLazy r) :: stack) t0)
                   else norm cfg env1 stack t0)
          | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
              (match stack with
               | (UnivArgs uu____12410)::uu____12411 ->
                   failwith
                     "Ill-typed term: universes cannot be applied to term abstraction"
               | (Match uu____12420)::uu____12421 ->
                   failwith
                     "Ill-typed term: cannot pattern match an abstraction"
               | (Arg (c,uu____12433,uu____12434))::stack_rest ->
                   (match c with
                    | Univ uu____12438 ->
                        norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                          stack_rest t1
                    | uu____12447 ->
                        (match bs with
                         | [] -> failwith "Impossible"
                         | b::[] ->
                             let uu____12465 =
                               log cfg
                                 (fun uu____12468  ->
                                    let uu____12469 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12469)
                                in
                             norm cfg (((FStar_Pervasives_Native.Some b), c)
                               :: env) stack_rest body
                         | b::tl1 ->
                             let uu____12506 =
                               log cfg
                                 (fun uu____12509  ->
                                    let uu____12510 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12510)
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
                   let uu____12558 = set_memo cfg r (env, t1)  in
                   let uu____12585 =
                     log cfg
                       (fun uu____12588  ->
                          let uu____12589 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12589)
                      in
                   norm cfg env stack1 t1
               | (Debug uu____12590)::uu____12591 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_12601 = cfg.steps  in
                            {
                              beta = (uu___153_12601.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_12601.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_12601.unfold_until);
                              unfold_only = (uu___153_12601.unfold_only);
                              unfold_fully = (uu___153_12601.unfold_fully);
                              unfold_attr = (uu___153_12601.unfold_attr);
                              unfold_tac = (uu___153_12601.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_12601.erase_universes);
                              allow_unbound_universes =
                                (uu___153_12601.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_12601.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_12601.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_12601.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_12603 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_12603.tcenv);
                              debug = (uu___154_12603.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_12603.primitive_steps);
                              strong = (uu___154_12603.strong);
                              memoize_lazy = (uu___154_12603.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_12603.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____12605 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____12605 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____12647  -> dummy :: env1) env)
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
                                         let uu____12684 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____12684)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_12689 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_12689.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_12689.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____12690 -> lopt  in
                          let uu____12693 =
                            log cfg
                              (fun uu____12696  ->
                                 let uu____12697 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12697)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_12706 = cfg  in
                            {
                              steps = (uu___156_12706.steps);
                              tcenv = (uu___156_12706.tcenv);
                              debug = (uu___156_12706.debug);
                              delta_level = (uu___156_12706.delta_level);
                              primitive_steps =
                                (uu___156_12706.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_12706.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_12706.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (Meta uu____12717)::uu____12718 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_12730 = cfg.steps  in
                            {
                              beta = (uu___153_12730.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_12730.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_12730.unfold_until);
                              unfold_only = (uu___153_12730.unfold_only);
                              unfold_fully = (uu___153_12730.unfold_fully);
                              unfold_attr = (uu___153_12730.unfold_attr);
                              unfold_tac = (uu___153_12730.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_12730.erase_universes);
                              allow_unbound_universes =
                                (uu___153_12730.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_12730.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_12730.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_12730.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_12732 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_12732.tcenv);
                              debug = (uu___154_12732.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_12732.primitive_steps);
                              strong = (uu___154_12732.strong);
                              memoize_lazy = (uu___154_12732.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_12732.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____12734 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____12734 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____12776  -> dummy :: env1) env)
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
                                         let uu____12813 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____12813)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_12818 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_12818.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_12818.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____12819 -> lopt  in
                          let uu____12822 =
                            log cfg
                              (fun uu____12825  ->
                                 let uu____12826 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12826)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_12835 = cfg  in
                            {
                              steps = (uu___156_12835.steps);
                              tcenv = (uu___156_12835.tcenv);
                              debug = (uu___156_12835.debug);
                              delta_level = (uu___156_12835.delta_level);
                              primitive_steps =
                                (uu___156_12835.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_12835.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_12835.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (Let uu____12846)::uu____12847 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_12861 = cfg.steps  in
                            {
                              beta = (uu___153_12861.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_12861.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_12861.unfold_until);
                              unfold_only = (uu___153_12861.unfold_only);
                              unfold_fully = (uu___153_12861.unfold_fully);
                              unfold_attr = (uu___153_12861.unfold_attr);
                              unfold_tac = (uu___153_12861.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_12861.erase_universes);
                              allow_unbound_universes =
                                (uu___153_12861.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_12861.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_12861.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_12861.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_12863 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_12863.tcenv);
                              debug = (uu___154_12863.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_12863.primitive_steps);
                              strong = (uu___154_12863.strong);
                              memoize_lazy = (uu___154_12863.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_12863.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____12865 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____12865 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____12907  -> dummy :: env1) env)
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
                                         let uu____12944 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____12944)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_12949 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_12949.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_12949.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____12950 -> lopt  in
                          let uu____12953 =
                            log cfg
                              (fun uu____12956  ->
                                 let uu____12957 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12957)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_12966 = cfg  in
                            {
                              steps = (uu___156_12966.steps);
                              tcenv = (uu___156_12966.tcenv);
                              debug = (uu___156_12966.debug);
                              delta_level = (uu___156_12966.delta_level);
                              primitive_steps =
                                (uu___156_12966.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_12966.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_12966.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (App uu____12977)::uu____12978 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_12992 = cfg.steps  in
                            {
                              beta = (uu___153_12992.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_12992.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_12992.unfold_until);
                              unfold_only = (uu___153_12992.unfold_only);
                              unfold_fully = (uu___153_12992.unfold_fully);
                              unfold_attr = (uu___153_12992.unfold_attr);
                              unfold_tac = (uu___153_12992.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_12992.erase_universes);
                              allow_unbound_universes =
                                (uu___153_12992.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_12992.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_12992.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_12992.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_12994 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_12994.tcenv);
                              debug = (uu___154_12994.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_12994.primitive_steps);
                              strong = (uu___154_12994.strong);
                              memoize_lazy = (uu___154_12994.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_12994.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____12996 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____12996 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13038  -> dummy :: env1) env)
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
                                         let uu____13075 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13075)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13080 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13080.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13080.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13081 -> lopt  in
                          let uu____13084 =
                            log cfg
                              (fun uu____13087  ->
                                 let uu____13088 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13088)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13097 = cfg  in
                            {
                              steps = (uu___156_13097.steps);
                              tcenv = (uu___156_13097.tcenv);
                              debug = (uu___156_13097.debug);
                              delta_level = (uu___156_13097.delta_level);
                              primitive_steps =
                                (uu___156_13097.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13097.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13097.normalize_pure_lets)
                            }  in
                          norm cfg1 env'
                            ((Abs
                                (env, bs1, env', lopt1,
                                  (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                            body1)
               | (Abs uu____13108)::uu____13109 ->
                   if (cfg.steps).weak
                   then
                     let t2 =
                       if (cfg.steps).in_full_norm_request
                       then closure_as_term cfg env t1
                       else
                         (let steps' =
                            let uu___153_13127 = cfg.steps  in
                            {
                              beta = (uu___153_13127.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_13127.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_13127.unfold_until);
                              unfold_only = (uu___153_13127.unfold_only);
                              unfold_fully = (uu___153_13127.unfold_fully);
                              unfold_attr = (uu___153_13127.unfold_attr);
                              unfold_tac = (uu___153_13127.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_13127.erase_universes);
                              allow_unbound_universes =
                                (uu___153_13127.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_13127.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_13127.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_13127.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_13129 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_13129.tcenv);
                              debug = (uu___154_13129.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_13129.primitive_steps);
                              strong = (uu___154_13129.strong);
                              memoize_lazy = (uu___154_13129.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_13129.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____13131 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____13131 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13173  -> dummy :: env1) env)
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
                                         let uu____13210 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13210)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13215 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13215.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13215.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13216 -> lopt  in
                          let uu____13219 =
                            log cfg
                              (fun uu____13222  ->
                                 let uu____13223 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13223)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13232 = cfg  in
                            {
                              steps = (uu___156_13232.steps);
                              tcenv = (uu___156_13232.tcenv);
                              debug = (uu___156_13232.debug);
                              delta_level = (uu___156_13232.delta_level);
                              primitive_steps =
                                (uu___156_13232.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13232.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13232.normalize_pure_lets)
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
                            let uu___153_13246 = cfg.steps  in
                            {
                              beta = (uu___153_13246.beta);
                              iota = false;
                              zeta = false;
                              weak = false;
                              hnf = (uu___153_13246.hnf);
                              primops = false;
                              do_not_unfold_pure_lets = true;
                              unfold_until = (uu___153_13246.unfold_until);
                              unfold_only = (uu___153_13246.unfold_only);
                              unfold_fully = (uu___153_13246.unfold_fully);
                              unfold_attr = (uu___153_13246.unfold_attr);
                              unfold_tac = (uu___153_13246.unfold_tac);
                              pure_subterms_within_computations = false;
                              simplify = false;
                              erase_universes =
                                (uu___153_13246.erase_universes);
                              allow_unbound_universes =
                                (uu___153_13246.allow_unbound_universes);
                              reify_ = false;
                              compress_uvars =
                                (uu___153_13246.compress_uvars);
                              no_full_norm = true;
                              check_no_uvars =
                                (uu___153_13246.check_no_uvars);
                              unmeta = false;
                              unascribe = false;
                              in_full_norm_request =
                                (uu___153_13246.in_full_norm_request)
                            }  in
                          let cfg' =
                            let uu___154_13248 = cfg  in
                            {
                              steps = steps';
                              tcenv = (uu___154_13248.tcenv);
                              debug = (uu___154_13248.debug);
                              delta_level = [FStar_TypeChecker_Env.NoDelta];
                              primitive_steps =
                                (uu___154_13248.primitive_steps);
                              strong = (uu___154_13248.strong);
                              memoize_lazy = (uu___154_13248.memoize_lazy);
                              normalize_pure_lets =
                                (uu___154_13248.normalize_pure_lets)
                            }  in
                          norm cfg' env [] t1)
                        in
                     rebuild cfg env stack t2
                   else
                     (let uu____13250 = FStar_Syntax_Subst.open_term' bs body
                         in
                      match uu____13250 with
                      | (bs1,body1,opening) ->
                          let env' =
                            FStar_All.pipe_right bs1
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun uu____13292  -> dummy :: env1) env)
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
                                         let uu____13329 =
                                           FStar_Syntax_Subst.subst opening
                                             t2
                                            in
                                         norm cfg env' [] uu____13329)
                                  else
                                    FStar_Util.map_opt
                                      rc.FStar_Syntax_Syntax.residual_typ
                                      (FStar_Syntax_Subst.subst opening)
                                   in
                                FStar_Pervasives_Native.Some
                                  (let uu___155_13334 = rc  in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___155_13334.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ = rct;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___155_13334.FStar_Syntax_Syntax.residual_flags)
                                   })
                            | uu____13335 -> lopt  in
                          let uu____13338 =
                            log cfg
                              (fun uu____13341  ->
                                 let uu____13342 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13342)
                             in
                          let stack1 = (Cfg cfg) :: stack  in
                          let cfg1 =
                            let uu___156_13351 = cfg  in
                            {
                              steps = (uu___156_13351.steps);
                              tcenv = (uu___156_13351.tcenv);
                              debug = (uu___156_13351.debug);
                              delta_level = (uu___156_13351.delta_level);
                              primitive_steps =
                                (uu___156_13351.primitive_steps);
                              strong = true;
                              memoize_lazy = (uu___156_13351.memoize_lazy);
                              normalize_pure_lets =
                                (uu___156_13351.normalize_pure_lets)
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
                     (fun uu____13400  ->
                        fun stack1  ->
                          match uu____13400 with
                          | (a,aq) ->
                              let uu____13412 =
                                let uu____13413 =
                                  let uu____13420 =
                                    let uu____13421 =
                                      let uu____13452 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (env, a, uu____13452, false)  in
                                    Clos uu____13421  in
                                  (uu____13420, aq,
                                    (t1.FStar_Syntax_Syntax.pos))
                                   in
                                Arg uu____13413  in
                              uu____13412 :: stack1) args)
                 in
              let uu____13533 =
                log cfg
                  (fun uu____13536  ->
                     let uu____13537 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13537)
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
                            ((let uu___157_13573 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___157_13573.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___157_13573.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), f)) t1.FStar_Syntax_Syntax.pos
                        in
                     rebuild cfg env stack t2
                 | uu____13574 ->
                     let uu____13579 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13579)
              else
                (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                 let uu____13582 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 match uu____13582 with
                 | (closing,f1) ->
                     let f2 = norm cfg (dummy :: env) [] f1  in
                     let t2 =
                       let uu____13613 =
                         let uu____13614 =
                           let uu____13621 =
                             FStar_Syntax_Subst.close closing f2  in
                           ((let uu___158_13623 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_13623.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_13623.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t_x
                             }), uu____13621)
                            in
                         FStar_Syntax_Syntax.Tm_refine uu____13614  in
                       mk uu____13613 t1.FStar_Syntax_Syntax.pos  in
                     rebuild cfg env stack t2)
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (cfg.steps).weak
              then
                let uu____13642 = closure_as_term cfg env t1  in
                rebuild cfg env stack uu____13642
              else
                (let uu____13644 = FStar_Syntax_Subst.open_comp bs c  in
                 match uu____13644 with
                 | (bs1,c1) ->
                     let c2 =
                       let uu____13652 =
                         FStar_All.pipe_right bs1
                           (FStar_List.fold_left
                              (fun env1  -> fun uu____13676  -> dummy :: env1)
                              env)
                          in
                       norm_comp cfg uu____13652 c1  in
                     let t2 =
                       let uu____13698 = norm_binders cfg env bs1  in
                       FStar_Syntax_Util.arrow uu____13698 c2  in
                     rebuild cfg env stack t2)
          | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
              (cfg.steps).unascribe -> norm cfg env stack t11
          | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
              (match stack with
               | (Match uu____13809)::uu____13810 ->
                   let uu____13821 =
                     log cfg
                       (fun uu____13823  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | (Arg uu____13824)::uu____13825 ->
                   let uu____13834 =
                     log cfg
                       (fun uu____13836  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | (App
                   (uu____13837,{
                                  FStar_Syntax_Syntax.n =
                                    FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reify );
                                  FStar_Syntax_Syntax.pos = uu____13838;
                                  FStar_Syntax_Syntax.vars = uu____13839;_},uu____13840,uu____13841))::uu____13842
                   ->
                   let uu____13849 =
                     log cfg
                       (fun uu____13851  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | (MemoLazy uu____13852)::uu____13853 ->
                   let uu____13862 =
                     log cfg
                       (fun uu____13864  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n")
                      in
                   norm cfg env stack t11
               | uu____13865 ->
                   let uu____13866 =
                     log cfg
                       (fun uu____13868  ->
                          FStar_Util.print_string "+++ Keeping ascription \n")
                      in
                   let t12 = norm cfg env [] t11  in
                   let uu____13870 =
                     log cfg
                       (fun uu____13872  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n")
                      in
                   let tc1 =
                     match tc with
                     | FStar_Util.Inl t2 ->
                         let uu____13889 = norm cfg env [] t2  in
                         FStar_Util.Inl uu____13889
                     | FStar_Util.Inr c ->
                         let uu____13897 = norm_comp cfg env c  in
                         FStar_Util.Inr uu____13897
                      in
                   let tacopt1 = FStar_Util.map_opt tacopt (norm cfg env [])
                      in
                   (match stack with
                    | (Cfg cfg1)::stack1 ->
                        let t2 =
                          let uu____13910 =
                            let uu____13911 =
                              let uu____13938 =
                                FStar_Syntax_Util.unascribe t12  in
                              (uu____13938, (tc1, tacopt1), l)  in
                            FStar_Syntax_Syntax.Tm_ascribed uu____13911  in
                          mk uu____13910 t1.FStar_Syntax_Syntax.pos  in
                        norm cfg1 env stack1 t2
                    | uu____13957 ->
                        let uu____13958 =
                          let uu____13959 =
                            let uu____13960 =
                              let uu____13987 =
                                FStar_Syntax_Util.unascribe t12  in
                              (uu____13987, (tc1, tacopt1), l)  in
                            FStar_Syntax_Syntax.Tm_ascribed uu____13960  in
                          mk uu____13959 t1.FStar_Syntax_Syntax.pos  in
                        rebuild cfg env stack uu____13958))
          | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
              let stack1 =
                (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos))) ::
                stack  in
              let cfg1 =
                if (cfg.steps).iota
                then
                  let uu___159_14064 = cfg  in
                  {
                    steps =
                      (let uu___160_14067 = cfg.steps  in
                       {
                         beta = (uu___160_14067.beta);
                         iota = (uu___160_14067.iota);
                         zeta = (uu___160_14067.zeta);
                         weak = true;
                         hnf = (uu___160_14067.hnf);
                         primops = (uu___160_14067.primops);
                         do_not_unfold_pure_lets =
                           (uu___160_14067.do_not_unfold_pure_lets);
                         unfold_until = (uu___160_14067.unfold_until);
                         unfold_only = (uu___160_14067.unfold_only);
                         unfold_fully = (uu___160_14067.unfold_fully);
                         unfold_attr = (uu___160_14067.unfold_attr);
                         unfold_tac = (uu___160_14067.unfold_tac);
                         pure_subterms_within_computations =
                           (uu___160_14067.pure_subterms_within_computations);
                         simplify = (uu___160_14067.simplify);
                         erase_universes = (uu___160_14067.erase_universes);
                         allow_unbound_universes =
                           (uu___160_14067.allow_unbound_universes);
                         reify_ = (uu___160_14067.reify_);
                         compress_uvars = (uu___160_14067.compress_uvars);
                         no_full_norm = (uu___160_14067.no_full_norm);
                         check_no_uvars = (uu___160_14067.check_no_uvars);
                         unmeta = (uu___160_14067.unmeta);
                         unascribe = (uu___160_14067.unascribe);
                         in_full_norm_request =
                           (uu___160_14067.in_full_norm_request)
                       });
                    tcenv = (uu___159_14064.tcenv);
                    debug = (uu___159_14064.debug);
                    delta_level = (uu___159_14064.delta_level);
                    primitive_steps = (uu___159_14064.primitive_steps);
                    strong = (uu___159_14064.strong);
                    memoize_lazy = (uu___159_14064.memoize_lazy);
                    normalize_pure_lets =
                      (uu___159_14064.normalize_pure_lets)
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
                        let uu____14103 =
                          FStar_Syntax_Subst.univ_var_opening
                            lb.FStar_Syntax_Syntax.lbunivs
                           in
                        match uu____14103 with
                        | (openings,lbunivs) ->
                            let cfg1 =
                              let uu___161_14123 = cfg  in
                              let uu____14124 =
                                FStar_TypeChecker_Env.push_univ_vars
                                  cfg.tcenv lbunivs
                                 in
                              {
                                steps = (uu___161_14123.steps);
                                tcenv = uu____14124;
                                debug = (uu___161_14123.debug);
                                delta_level = (uu___161_14123.delta_level);
                                primitive_steps =
                                  (uu___161_14123.primitive_steps);
                                strong = (uu___161_14123.strong);
                                memoize_lazy = (uu___161_14123.memoize_lazy);
                                normalize_pure_lets =
                                  (uu___161_14123.normalize_pure_lets)
                              }  in
                            let norm1 t2 =
                              let uu____14130 =
                                let uu____14131 =
                                  FStar_Syntax_Subst.subst openings t2  in
                                norm cfg1 env [] uu____14131  in
                              FStar_Syntax_Subst.close_univ_vars lbunivs
                                uu____14130
                               in
                            let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                               in
                            let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                               in
                            let uu___162_14134 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___162_14134.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = lbunivs;
                              FStar_Syntax_Syntax.lbtyp = lbtyp;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___162_14134.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___162_14134.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___162_14134.FStar_Syntax_Syntax.lbpos)
                            }))
                 in
              let uu____14135 =
                mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                  t1.FStar_Syntax_Syntax.pos
                 in
              rebuild cfg env stack uu____14135
          | FStar_Syntax_Syntax.Tm_let
              ((uu____14146,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____14147;
                              FStar_Syntax_Syntax.lbunivs = uu____14148;
                              FStar_Syntax_Syntax.lbtyp = uu____14149;
                              FStar_Syntax_Syntax.lbeff = uu____14150;
                              FStar_Syntax_Syntax.lbdef = uu____14151;
                              FStar_Syntax_Syntax.lbattrs = uu____14152;
                              FStar_Syntax_Syntax.lbpos = uu____14153;_}::uu____14154),uu____14155)
              -> rebuild cfg env stack t1
          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
              let n1 =
                FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                  lb.FStar_Syntax_Syntax.lbeff
                 in
              let uu____14195 =
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
              if uu____14195
              then
                let binder =
                  let uu____14197 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.mk_binder uu____14197  in
                let env1 =
                  let uu____14207 =
                    let uu____14214 =
                      let uu____14215 =
                        let uu____14246 =
                          FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                        (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14246,
                          false)
                         in
                      Clos uu____14215  in
                    ((FStar_Pervasives_Native.Some binder), uu____14214)  in
                  uu____14207 :: env  in
                let uu____14337 =
                  log cfg
                    (fun uu____14339  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n")
                   in
                norm cfg env1 stack body
              else
                if (cfg.steps).weak
                then
                  (let uu____14341 =
                     log cfg
                       (fun uu____14343  ->
                          FStar_Util.print_string "+++ Not touching Tm_let\n")
                      in
                   let uu____14344 = closure_as_term cfg env t1  in
                   rebuild cfg env stack uu____14344)
                else
                  (let uu____14346 =
                     let uu____14351 =
                       let uu____14352 =
                         let uu____14353 =
                           FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                             FStar_Util.left
                            in
                         FStar_All.pipe_right uu____14353
                           FStar_Syntax_Syntax.mk_binder
                          in
                       [uu____14352]  in
                     FStar_Syntax_Subst.open_term uu____14351 body  in
                   match uu____14346 with
                   | (bs,body1) ->
                       let uu____14360 =
                         log cfg
                           (fun uu____14362  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type")
                          in
                       let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                          in
                       let lbname =
                         let x =
                           let uu____14370 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____14370  in
                         FStar_Util.Inl
                           (let uu___163_14380 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___163_14380.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___163_14380.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            })
                          in
                       let uu____14381 =
                         log cfg
                           (fun uu____14383  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- definiens\n")
                          in
                       let lb1 =
                         let uu___164_14385 = lb  in
                         let uu____14386 =
                           norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                         {
                           FStar_Syntax_Syntax.lbname = lbname;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___164_14385.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = ty;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___164_14385.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = uu____14386;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___164_14385.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___164_14385.FStar_Syntax_Syntax.lbpos)
                         }  in
                       let env' =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun env1  -> fun uu____14421  -> dummy :: env1)
                              env)
                          in
                       let stack1 = (Cfg cfg) :: stack  in
                       let cfg1 =
                         let uu___165_14444 = cfg  in
                         {
                           steps = (uu___165_14444.steps);
                           tcenv = (uu___165_14444.tcenv);
                           debug = (uu___165_14444.debug);
                           delta_level = (uu___165_14444.delta_level);
                           primitive_steps = (uu___165_14444.primitive_steps);
                           strong = true;
                           memoize_lazy = (uu___165_14444.memoize_lazy);
                           normalize_pure_lets =
                             (uu___165_14444.normalize_pure_lets)
                         }  in
                       let uu____14445 =
                         log cfg1
                           (fun uu____14447  ->
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
              let uu____14464 = FStar_Syntax_Subst.open_let_rec lbs body  in
              (match uu____14464 with
               | (lbs1,body1) ->
                   let lbs2 =
                     FStar_List.map
                       (fun lb  ->
                          let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let uu____14500 =
                              let uu___166_14501 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_14501.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___166_14501.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }  in
                            FStar_Util.Inl uu____14500  in
                          let uu____14502 =
                            FStar_Syntax_Util.abs_formals
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          match uu____14502 with
                          | (xs,def_body,lopt) ->
                              let xs1 = norm_binders cfg env xs  in
                              let env1 =
                                let uu____14528 =
                                  FStar_List.map (fun uu____14544  -> dummy)
                                    lbs1
                                   in
                                let uu____14545 =
                                  let uu____14554 =
                                    FStar_List.map
                                      (fun uu____14574  -> dummy) xs1
                                     in
                                  FStar_List.append uu____14554 env  in
                                FStar_List.append uu____14528 uu____14545  in
                              let def_body1 = norm cfg env1 [] def_body  in
                              let lopt1 =
                                match lopt with
                                | FStar_Pervasives_Native.Some rc ->
                                    let uu____14598 =
                                      let uu___167_14599 = rc  in
                                      let uu____14600 =
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (norm cfg env1 [])
                                         in
                                      {
                                        FStar_Syntax_Syntax.residual_effect =
                                          (uu___167_14599.FStar_Syntax_Syntax.residual_effect);
                                        FStar_Syntax_Syntax.residual_typ =
                                          uu____14600;
                                        FStar_Syntax_Syntax.residual_flags =
                                          (uu___167_14599.FStar_Syntax_Syntax.residual_flags)
                                      }  in
                                    FStar_Pervasives_Native.Some uu____14598
                                | uu____14607 -> lopt  in
                              let def =
                                FStar_Syntax_Util.abs xs1 def_body1 lopt1  in
                              let uu___168_14611 = lb  in
                              {
                                FStar_Syntax_Syntax.lbname = lbname;
                                FStar_Syntax_Syntax.lbunivs =
                                  (uu___168_14611.FStar_Syntax_Syntax.lbunivs);
                                FStar_Syntax_Syntax.lbtyp = ty;
                                FStar_Syntax_Syntax.lbeff =
                                  (uu___168_14611.FStar_Syntax_Syntax.lbeff);
                                FStar_Syntax_Syntax.lbdef = def;
                                FStar_Syntax_Syntax.lbattrs =
                                  (uu___168_14611.FStar_Syntax_Syntax.lbattrs);
                                FStar_Syntax_Syntax.lbpos =
                                  (uu___168_14611.FStar_Syntax_Syntax.lbpos)
                              }) lbs1
                      in
                   let env' =
                     let uu____14621 =
                       FStar_List.map (fun uu____14637  -> dummy) lbs2  in
                     FStar_List.append uu____14621 env  in
                   let body2 = norm cfg env' [] body1  in
                   let uu____14645 =
                     FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                   (match uu____14645 with
                    | (lbs3,body3) ->
                        let t2 =
                          let uu___169_14661 = t1  in
                          {
                            FStar_Syntax_Syntax.n =
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs3), body3));
                            FStar_Syntax_Syntax.pos =
                              (uu___169_14661.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___169_14661.FStar_Syntax_Syntax.vars)
                          }  in
                        rebuild cfg env stack t2))
          | FStar_Syntax_Syntax.Tm_let (lbs,body) when
              Prims.op_Negation (cfg.steps).zeta ->
              let uu____14688 = closure_as_term cfg env t1  in
              rebuild cfg env stack uu____14688
          | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
              let uu____14707 =
                FStar_List.fold_right
                  (fun lb  ->
                     fun uu____14783  ->
                       match uu____14783 with
                       | (rec_env,memos,i) ->
                           let bv =
                             let uu___170_14904 =
                               FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___170_14904.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index = i;
                               FStar_Syntax_Syntax.sort =
                                 (uu___170_14904.FStar_Syntax_Syntax.sort)
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
              (match uu____14707 with
               | (rec_env,memos,uu____15117) ->
                   let uu____15170 =
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
                            let uu____15493 =
                              let uu____15500 =
                                let uu____15501 =
                                  let uu____15532 =
                                    FStar_Util.mk_ref
                                      FStar_Pervasives_Native.None
                                     in
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                    uu____15532, false)
                                   in
                                Clos uu____15501  in
                              (FStar_Pervasives_Native.None, uu____15500)  in
                            uu____15493 :: env1)
                       (FStar_Pervasives_Native.snd lbs) env
                      in
                   norm cfg body_env stack body)
          | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
              let uu____15639 =
                log cfg
                  (fun uu____15642  ->
                     let uu____15643 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15643)
                 in
              (match m with
               | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                   reduce_impure_comp cfg env stack head1 (FStar_Util.Inl m1)
                     t2
               | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                   reduce_impure_comp cfg env stack head1
                     (FStar_Util.Inr (m1, m')) t2
               | uu____15665 ->
                   if (cfg.steps).unmeta
                   then norm cfg env stack head1
                   else
                     (match stack with
                      | uu____15667::uu____15668 ->
                          (match m with
                           | FStar_Syntax_Syntax.Meta_labeled
                               (l,r,uu____15673) ->
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
                           | uu____15696 -> norm cfg env stack head1)
                      | [] ->
                          let head2 = norm cfg env [] head1  in
                          let m1 =
                            match m with
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let uu____15710 =
                                  norm_pattern_args cfg env args  in
                                FStar_Syntax_Syntax.Meta_pattern uu____15710
                            | uu____15721 -> m  in
                          let t2 =
                            mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack t2))
          | FStar_Syntax_Syntax.Tm_delayed uu____15725 ->
              let t2 = FStar_Syntax_Subst.compress t1  in
              norm cfg env stack t2
          | FStar_Syntax_Syntax.Tm_uvar uu____15751 ->
              let t2 = FStar_Syntax_Subst.compress t1  in
              (match t2.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uvar uu____15769 ->
                   if (cfg.steps).check_no_uvars
                   then
                     let uu____15786 =
                       let uu____15787 =
                         FStar_Range.string_of_range
                           t2.FStar_Syntax_Syntax.pos
                          in
                       let uu____15788 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format2
                         "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                         uu____15787 uu____15788
                        in
                     failwith uu____15786
                   else rebuild cfg env stack t2
               | uu____15790 -> norm cfg env stack t2)

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
                let uu____15800 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____15800  in
              let uu____15801 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15801 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15812 =
                    log cfg
                      (fun uu____15814  ->
                         FStar_Util.print "Tm_fvar case 2\n" [])
                     in
                  rebuild cfg env stack t0
              | FStar_Pervasives_Native.Some (us,t) ->
                  let uu____15821 =
                    log cfg
                      (fun uu____15825  ->
                         let uu____15826 =
                           FStar_Syntax_Print.term_to_string t0  in
                         let uu____15827 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 ">>> Unfolded %s to %s\n"
                           uu____15826 uu____15827)
                     in
                  let t1 =
                    if
                      ((cfg.steps).unfold_until =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Delta_constant))
                        && (Prims.op_Negation (cfg.steps).unfold_tac)
                    then t
                    else
                      (let uu____15832 =
                         FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_Syntax_Subst.set_use_range uu____15832 t)
                     in
                  let n1 = FStar_List.length us  in
                  if n1 > (Prims.parse_int "0")
                  then
                    (match stack with
                     | (UnivArgs (us',uu____15841))::stack1 ->
                         let env1 =
                           FStar_All.pipe_right us'
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun u  ->
                                     (FStar_Pervasives_Native.None, (Univ u))
                                     :: env1) env)
                            in
                         norm cfg env1 stack1 t1
                     | uu____15896 when
                         (cfg.steps).erase_universes ||
                           (cfg.steps).allow_unbound_universes
                         -> norm cfg env stack t1
                     | uu____15899 ->
                         let uu____15902 =
                           let uu____15903 =
                             FStar_Syntax_Print.lid_to_string
                               (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              in
                           FStar_Util.format1
                             "Impossible: missing universe instantiation on %s"
                             uu____15903
                            in
                         failwith uu____15902)
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
                  let uu___171_15927 = cfg  in
                  let uu____15928 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____15928;
                    tcenv = (uu___171_15927.tcenv);
                    debug = (uu___171_15927.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_15927.primitive_steps);
                    strong = (uu___171_15927.strong);
                    memoize_lazy = (uu___171_15927.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_15927.normalize_pure_lets)
                  }
                else
                  (let uu___172_15930 = cfg  in
                   {
                     steps =
                       (let uu___173_15933 = cfg.steps  in
                        {
                          beta = (uu___173_15933.beta);
                          iota = (uu___173_15933.iota);
                          zeta = false;
                          weak = (uu___173_15933.weak);
                          hnf = (uu___173_15933.hnf);
                          primops = (uu___173_15933.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_15933.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_15933.unfold_until);
                          unfold_only = (uu___173_15933.unfold_only);
                          unfold_fully = (uu___173_15933.unfold_fully);
                          unfold_attr = (uu___173_15933.unfold_attr);
                          unfold_tac = (uu___173_15933.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_15933.pure_subterms_within_computations);
                          simplify = (uu___173_15933.simplify);
                          erase_universes = (uu___173_15933.erase_universes);
                          allow_unbound_universes =
                            (uu___173_15933.allow_unbound_universes);
                          reify_ = (uu___173_15933.reify_);
                          compress_uvars = (uu___173_15933.compress_uvars);
                          no_full_norm = (uu___173_15933.no_full_norm);
                          check_no_uvars = (uu___173_15933.check_no_uvars);
                          unmeta = (uu___173_15933.unmeta);
                          unascribe = (uu___173_15933.unascribe);
                          in_full_norm_request =
                            (uu___173_15933.in_full_norm_request)
                        });
                     tcenv = (uu___172_15930.tcenv);
                     debug = (uu___172_15930.debug);
                     delta_level = (uu___172_15930.delta_level);
                     primitive_steps = (uu___172_15930.primitive_steps);
                     strong = (uu___172_15930.strong);
                     memoize_lazy = (uu___172_15930.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_15930.normalize_pure_lets)
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
                let uu____15959 =
                  log cfg
                    (fun uu____15963  ->
                       let uu____15964 = FStar_Syntax_Print.tag_of_term head2
                          in
                       let uu____15965 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print2 "Reifying: (%s) %s\n" uu____15964
                         uu____15965)
                   in
                let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                let uu____15967 =
                  let uu____15968 = FStar_Syntax_Subst.compress head3  in
                  uu____15968.FStar_Syntax_Syntax.n  in
                match uu____15967 with
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let ed =
                      let uu____15986 =
                        FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                      FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                        uu____15986
                       in
                    let uu____15987 = ed.FStar_Syntax_Syntax.bind_repr  in
                    (match uu____15987 with
                     | (uu____15988,bind_repr) ->
                         (match lb.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____15994 ->
                              failwith "Cannot reify a top-level let binding"
                          | FStar_Util.Inl x ->
                              let is_return e =
                                let uu____16003 =
                                  let uu____16004 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16004.FStar_Syntax_Syntax.n  in
                                match uu____16003 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e1,FStar_Syntax_Syntax.Meta_monadic
                                     (uu____16010,uu____16011))
                                    ->
                                    let uu____16020 =
                                      let uu____16021 =
                                        FStar_Syntax_Subst.compress e1  in
                                      uu____16021.FStar_Syntax_Syntax.n  in
                                    (match uu____16020 with
                                     | FStar_Syntax_Syntax.Tm_meta
                                         (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                          (uu____16027,msrc,uu____16029))
                                         when
                                         FStar_Syntax_Util.is_pure_effect
                                           msrc
                                         ->
                                         let uu____16038 =
                                           FStar_Syntax_Subst.compress e2  in
                                         FStar_Pervasives_Native.Some
                                           uu____16038
                                     | uu____16039 ->
                                         FStar_Pervasives_Native.None)
                                | uu____16040 -> FStar_Pervasives_Native.None
                                 in
                              let uu____16041 =
                                is_return lb.FStar_Syntax_Syntax.lbdef  in
                              (match uu____16041 with
                               | FStar_Pervasives_Native.Some e ->
                                   let lb1 =
                                     let uu___174_16046 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___174_16046.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___174_16046.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___174_16046.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         FStar_Parser_Const.effect_PURE_lid;
                                       FStar_Syntax_Syntax.lbdef = e;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___174_16046.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___174_16046.FStar_Syntax_Syntax.lbpos)
                                     }  in
                                   let uu____16047 = FStar_List.tl stack  in
                                   let uu____16048 =
                                     let uu____16049 =
                                       let uu____16054 =
                                         let uu____16055 =
                                           let uu____16068 =
                                             FStar_Syntax_Util.mk_reify body
                                              in
                                           ((false, [lb1]), uu____16068)  in
                                         FStar_Syntax_Syntax.Tm_let
                                           uu____16055
                                          in
                                       FStar_Syntax_Syntax.mk uu____16054  in
                                     uu____16049 FStar_Pervasives_Native.None
                                       head3.FStar_Syntax_Syntax.pos
                                      in
                                   norm cfg env uu____16047 uu____16048
                               | FStar_Pervasives_Native.None  ->
                                   let uu____16084 =
                                     let uu____16085 = is_return body  in
                                     match uu____16085 with
                                     | FStar_Pervasives_Native.Some
                                         {
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_bvar y;
                                           FStar_Syntax_Syntax.pos =
                                             uu____16089;
                                           FStar_Syntax_Syntax.vars =
                                             uu____16090;_}
                                         -> FStar_Syntax_Syntax.bv_eq x y
                                     | uu____16095 -> false  in
                                   if uu____16084
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
                                        let uu____16118 =
                                          let uu____16123 =
                                            let uu____16124 =
                                              let uu____16141 =
                                                let uu____16144 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x
                                                   in
                                                [uu____16144]  in
                                              (uu____16141, body1,
                                                (FStar_Pervasives_Native.Some
                                                   body_rc))
                                               in
                                            FStar_Syntax_Syntax.Tm_abs
                                              uu____16124
                                             in
                                          FStar_Syntax_Syntax.mk uu____16123
                                           in
                                        uu____16118
                                          FStar_Pervasives_Native.None
                                          body1.FStar_Syntax_Syntax.pos
                                         in
                                      let close1 = closure_as_term cfg env
                                         in
                                      let bind_inst =
                                        let uu____16161 =
                                          let uu____16162 =
                                            FStar_Syntax_Subst.compress
                                              bind_repr
                                             in
                                          uu____16162.FStar_Syntax_Syntax.n
                                           in
                                        match uu____16161 with
                                        | FStar_Syntax_Syntax.Tm_uinst
                                            (bind1,uu____16168::uu____16169::[])
                                            ->
                                            let uu____16176 =
                                              let uu____16181 =
                                                let uu____16182 =
                                                  let uu____16189 =
                                                    let uu____16192 =
                                                      let uu____16193 =
                                                        close1
                                                          lb.FStar_Syntax_Syntax.lbtyp
                                                         in
                                                      (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                        cfg.tcenv uu____16193
                                                       in
                                                    let uu____16194 =
                                                      let uu____16197 =
                                                        let uu____16198 =
                                                          close1 t  in
                                                        (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.tcenv
                                                          uu____16198
                                                         in
                                                      [uu____16197]  in
                                                    uu____16192 ::
                                                      uu____16194
                                                     in
                                                  (bind1, uu____16189)  in
                                                FStar_Syntax_Syntax.Tm_uinst
                                                  uu____16182
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____16181
                                               in
                                            uu____16176
                                              FStar_Pervasives_Native.None
                                              rng
                                        | uu____16206 ->
                                            failwith
                                              "NIY : Reification of indexed effects"
                                         in
                                      let maybe_range_arg =
                                        let uu____16212 =
                                          FStar_Util.for_some
                                            (FStar_Syntax_Util.attr_eq
                                               FStar_Syntax_Util.dm4f_bind_range_attr)
                                            ed.FStar_Syntax_Syntax.eff_attrs
                                           in
                                        if uu____16212
                                        then
                                          let uu____16215 =
                                            let uu____16216 =
                                              FStar_Syntax_Embeddings.embed
                                                FStar_Syntax_Embeddings.e_range
                                                lb.FStar_Syntax_Syntax.lbpos
                                                lb.FStar_Syntax_Syntax.lbpos
                                               in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____16216
                                             in
                                          let uu____16217 =
                                            let uu____16220 =
                                              let uu____16221 =
                                                FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_range
                                                  body2.FStar_Syntax_Syntax.pos
                                                  body2.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____16221
                                               in
                                            [uu____16220]  in
                                          uu____16215 :: uu____16217
                                        else []  in
                                      let reified =
                                        let uu____16226 =
                                          let uu____16231 =
                                            let uu____16232 =
                                              let uu____16247 =
                                                let uu____16250 =
                                                  let uu____16253 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  let uu____16254 =
                                                    let uu____16257 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    [uu____16257]  in
                                                  uu____16253 :: uu____16254
                                                   in
                                                let uu____16258 =
                                                  let uu____16261 =
                                                    let uu____16264 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        FStar_Syntax_Syntax.tun
                                                       in
                                                    let uu____16265 =
                                                      let uu____16268 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          head4
                                                         in
                                                      let uu____16269 =
                                                        let uu____16272 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            FStar_Syntax_Syntax.tun
                                                           in
                                                        let uu____16273 =
                                                          let uu____16276 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              body2
                                                             in
                                                          [uu____16276]  in
                                                        uu____16272 ::
                                                          uu____16273
                                                         in
                                                      uu____16268 ::
                                                        uu____16269
                                                       in
                                                    uu____16264 ::
                                                      uu____16265
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____16261
                                                   in
                                                FStar_List.append uu____16250
                                                  uu____16258
                                                 in
                                              (bind_inst, uu____16247)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____16232
                                             in
                                          FStar_Syntax_Syntax.mk uu____16231
                                           in
                                        uu____16226
                                          FStar_Pervasives_Native.None rng
                                         in
                                      let uu____16284 =
                                        log cfg
                                          (fun uu____16288  ->
                                             let uu____16289 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____16290 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____16289 uu____16290)
                                         in
                                      let uu____16291 = FStar_List.tl stack
                                         in
                                      norm cfg env uu____16291 reified))))
                | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                    let ed =
                      let uu____16315 =
                        FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                      FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                        uu____16315
                       in
                    let uu____16316 = ed.FStar_Syntax_Syntax.bind_repr  in
                    (match uu____16316 with
                     | (uu____16317,bind_repr) ->
                         let maybe_unfold_action head4 =
                           let maybe_extract_fv t1 =
                             let t2 =
                               let uu____16354 =
                                 let uu____16355 =
                                   FStar_Syntax_Subst.compress t1  in
                                 uu____16355.FStar_Syntax_Syntax.n  in
                               match uu____16354 with
                               | FStar_Syntax_Syntax.Tm_uinst
                                   (t2,uu____16361) -> t2
                               | uu____16366 -> head4  in
                             let uu____16367 =
                               let uu____16368 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____16368.FStar_Syntax_Syntax.n  in
                             match uu____16367 with
                             | FStar_Syntax_Syntax.Tm_fvar x ->
                                 FStar_Pervasives_Native.Some x
                             | uu____16374 -> FStar_Pervasives_Native.None
                              in
                           let uu____16375 = maybe_extract_fv head4  in
                           match uu____16375 with
                           | FStar_Pervasives_Native.Some x when
                               let uu____16385 =
                                 FStar_Syntax_Syntax.lid_of_fv x  in
                               FStar_TypeChecker_Env.is_action cfg.tcenv
                                 uu____16385
                               ->
                               let head5 = norm cfg env [] head4  in
                               let action_unfolded =
                                 let uu____16390 = maybe_extract_fv head5  in
                                 match uu____16390 with
                                 | FStar_Pervasives_Native.Some uu____16395
                                     -> FStar_Pervasives_Native.Some true
                                 | uu____16396 ->
                                     FStar_Pervasives_Native.Some false
                                  in
                               (head5, action_unfolded)
                           | uu____16401 ->
                               (head4, FStar_Pervasives_Native.None)
                            in
                         let uu____16408 =
                           let is_arg_impure uu____16417 =
                             match uu____16417 with
                             | (e,q) ->
                                 let uu____16424 =
                                   let uu____16425 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16425.FStar_Syntax_Syntax.n  in
                                 (match uu____16424 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                       (m1,m2,t'))
                                      ->
                                      let uu____16440 =
                                        FStar_Syntax_Util.is_pure_effect m1
                                         in
                                      Prims.op_Negation uu____16440
                                  | uu____16441 -> false)
                              in
                           let uu____16442 =
                             let uu____16443 =
                               let uu____16450 =
                                 FStar_Syntax_Syntax.as_arg head_app  in
                               uu____16450 :: args  in
                             FStar_Util.for_some is_arg_impure uu____16443
                              in
                           if uu____16442
                           then
                             let uu____16455 =
                               let uu____16456 =
                                 FStar_Syntax_Print.term_to_string head3  in
                               FStar_Util.format1
                                 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                 uu____16456
                                in
                             failwith uu____16455
                           else ()  in
                         let uu____16458 = maybe_unfold_action head_app  in
                         (match uu____16458 with
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
                              let uu____16496 =
                                log cfg
                                  (fun uu____16500  ->
                                     let uu____16501 =
                                       FStar_Syntax_Print.term_to_string
                                         head0
                                        in
                                     let uu____16502 =
                                       FStar_Syntax_Print.term_to_string
                                         body1
                                        in
                                     FStar_Util.print2
                                       "Reified (2) <%s> to %s\n" uu____16501
                                       uu____16502)
                                 in
                              let uu____16503 = FStar_List.tl stack  in
                              norm cfg env uu____16503 body1))
                | FStar_Syntax_Syntax.Tm_meta
                    (e,FStar_Syntax_Syntax.Meta_monadic uu____16505) ->
                    do_reify_monadic fallback cfg env stack e m t
                | FStar_Syntax_Syntax.Tm_meta
                    (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                    ->
                    let lifted =
                      let uu____16529 = closure_as_term cfg env t'  in
                      reify_lift cfg e msrc mtgt uu____16529  in
                    let uu____16530 =
                      log cfg
                        (fun uu____16533  ->
                           let uu____16534 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16534)
                       in
                    let uu____16535 = FStar_List.tl stack  in
                    norm cfg env uu____16535 lifted
                | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                    let branches1 =
                      FStar_All.pipe_right branches
                        (FStar_List.map
                           (fun uu____16656  ->
                              match uu____16656 with
                              | (pat,wopt,tm) ->
                                  let uu____16704 =
                                    FStar_Syntax_Util.mk_reify tm  in
                                  (pat, wopt, uu____16704)))
                       in
                    let tm =
                      mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                        head3.FStar_Syntax_Syntax.pos
                       in
                    let uu____16736 = FStar_List.tl stack  in
                    norm cfg env uu____16736 tm
                | uu____16737 -> fallback ()

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
            let uu____16746 =
              log cfg
                (fun uu____16751  ->
                   let uu____16752 = FStar_Ident.string_of_lid msrc  in
                   let uu____16753 = FStar_Ident.string_of_lid mtgt  in
                   let uu____16754 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print3 "Reifying lift %s -> %s: %s\n"
                     uu____16752 uu____16753 uu____16754)
               in
            let uu____16755 =
              (FStar_Syntax_Util.is_pure_effect msrc) ||
                (FStar_Syntax_Util.is_div_effect msrc)
               in
            if uu____16755
            then
              let ed =
                let uu____16757 =
                  FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                FStar_TypeChecker_Env.get_effect_decl env uu____16757  in
              let uu____16758 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____16758 with
              | (uu____16759,return_repr) ->
                  let return_inst =
                    let uu____16768 =
                      let uu____16769 =
                        FStar_Syntax_Subst.compress return_repr  in
                      uu____16769.FStar_Syntax_Syntax.n  in
                    match uu____16768 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16775::[]) ->
                        let uu____16782 =
                          let uu____16787 =
                            let uu____16788 =
                              let uu____16795 =
                                let uu____16798 =
                                  env.FStar_TypeChecker_Env.universe_of env t
                                   in
                                [uu____16798]  in
                              (return_tm, uu____16795)  in
                            FStar_Syntax_Syntax.Tm_uinst uu____16788  in
                          FStar_Syntax_Syntax.mk uu____16787  in
                        uu____16782 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16806 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  let uu____16809 =
                    let uu____16814 =
                      let uu____16815 =
                        let uu____16830 =
                          let uu____16833 = FStar_Syntax_Syntax.as_arg t  in
                          let uu____16834 =
                            let uu____16837 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16837]  in
                          uu____16833 :: uu____16834  in
                        (return_inst, uu____16830)  in
                      FStar_Syntax_Syntax.Tm_app uu____16815  in
                    FStar_Syntax_Syntax.mk uu____16814  in
                  uu____16809 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16846 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____16846 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16849 =
                     let uu____16850 = FStar_Ident.text_of_lid msrc  in
                     let uu____16851 = FStar_Ident.text_of_lid mtgt  in
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       uu____16850 uu____16851
                      in
                   failwith uu____16849
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16852;
                     FStar_TypeChecker_Env.mtarget = uu____16853;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16854;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____16876 =
                     let uu____16877 = FStar_Ident.text_of_lid msrc  in
                     let uu____16878 = FStar_Ident.text_of_lid mtgt  in
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       uu____16877 uu____16878
                      in
                   failwith uu____16876
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16879;
                     FStar_TypeChecker_Env.mtarget = uu____16880;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16881;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16916 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____16917 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____16916 t FStar_Syntax_Syntax.tun uu____16917)

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
                (fun uu____16973  ->
                   match uu____16973 with
                   | (a,imp) ->
                       let uu____16984 = norm cfg env [] a  in
                       (uu____16984, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let uu____16988 =
          log cfg
            (fun uu____16992  ->
               let uu____16993 = FStar_Syntax_Print.comp_to_string comp  in
               let uu____16994 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
                 uu____16993 uu____16994)
           in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let t1 = norm cfg env [] t  in
            let uopt1 =
              match uopt with
              | FStar_Pervasives_Native.Some u ->
                  let uu____17018 = norm_universe cfg env u  in
                  FStar_All.pipe_left
                    (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                    uu____17018
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
               in
            let uu___175_17021 = comp  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t1, uopt1));
              FStar_Syntax_Syntax.pos =
                (uu___175_17021.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_17021.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let t1 = norm cfg env [] t  in
            let uopt1 =
              match uopt with
              | FStar_Pervasives_Native.Some u ->
                  let uu____17041 = norm_universe cfg env u  in
                  FStar_All.pipe_left
                    (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                    uu____17041
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
               in
            let uu___176_17044 = comp  in
            {
              FStar_Syntax_Syntax.n =
                (FStar_Syntax_Syntax.GTotal (t1, uopt1));
              FStar_Syntax_Syntax.pos =
                (uu___176_17044.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_17044.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args =
              FStar_List.mapi
                (fun idx  ->
                   fun uu____17078  ->
                     match uu____17078 with
                     | (a,i) ->
                         let uu____17089 = norm cfg env [] a  in
                         (uu____17089, i))
               in
            let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_17107  ->
                      match uu___90_17107 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17111 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____17111
                      | f -> f))
               in
            let comp_univs =
              FStar_List.map (norm_universe cfg env)
                ct.FStar_Syntax_Syntax.comp_univs
               in
            let result_typ =
              norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
            let uu___177_17119 = comp  in
            {
              FStar_Syntax_Syntax.n =
                (FStar_Syntax_Syntax.Comp
                   (let uu___178_17122 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_univs = comp_univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___178_17122.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ = result_typ;
                      FStar_Syntax_Syntax.effect_args = effect_args;
                      FStar_Syntax_Syntax.flags = flags1
                    }));
              FStar_Syntax_Syntax.pos =
                (uu___177_17119.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_17119.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17125  ->
        match uu____17125 with
        | (x,imp) ->
            let uu____17128 =
              let uu___179_17129 = x  in
              let uu____17130 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_17129.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_17129.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17130
              }  in
            (uu____17128, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17136 =
          FStar_List.fold_left
            (fun uu____17154  ->
               fun b  ->
                 match uu____17154 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17136 with | (nbs,uu____17194) -> FStar_List.rev nbs

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
            let uu____17210 =
              let uu___180_17211 = rc  in
              let uu____17212 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_17211.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17212;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_17211.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17210
        | uu____17219 -> lopt

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
          let uu____17239 =
            if (cfg.debug).b380
            then
              let uu____17240 = FStar_Syntax_Print.term_to_string tm  in
              let uu____17241 = FStar_Syntax_Print.term_to_string tm'  in
              FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
                (if (cfg.steps).simplify then "" else "NOT ") uu____17240
                uu____17241
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
          let uu____17261 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17261
          then tm1
          else
            (let w t =
               let uu___181_17274 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_17274.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_17274.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17284 =
                 let uu____17285 = FStar_Syntax_Util.unmeta t  in
                 uu____17285.FStar_Syntax_Syntax.n  in
               match uu____17284 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17292 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17339)::args1,(bv,uu____17342)::bs1) ->
                   let uu____17376 =
                     let uu____17377 = FStar_Syntax_Subst.compress t  in
                     uu____17377.FStar_Syntax_Syntax.n  in
                   (match uu____17376 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17381 -> false)
               | ([],[]) -> true
               | (uu____17402,uu____17403) -> false  in
             let is_applied bs t =
               let uu____17441 = FStar_Syntax_Util.head_and_args' t  in
               match uu____17441 with
               | (hd1,args) ->
                   let uu____17474 =
                     let uu____17475 = FStar_Syntax_Subst.compress hd1  in
                     uu____17475.FStar_Syntax_Syntax.n  in
                   (match uu____17474 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____17481 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____17495 = FStar_Syntax_Util.is_squash t  in
               match uu____17495 with
               | FStar_Pervasives_Native.Some (uu____17506,t') ->
                   is_applied bs t'
               | uu____17518 ->
                   let uu____17527 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____17527 with
                    | FStar_Pervasives_Native.Some (uu____17538,t') ->
                        is_applied bs t'
                    | uu____17550 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____17568 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17568 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17575)::(q,uu____17577)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____17612 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____17612 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____17617 =
                          let uu____17618 = FStar_Syntax_Subst.compress p  in
                          uu____17618.FStar_Syntax_Syntax.n  in
                        (match uu____17617 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17624 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____17624
                         | uu____17625 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____17628)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____17653 =
                          let uu____17654 = FStar_Syntax_Subst.compress p1
                             in
                          uu____17654.FStar_Syntax_Syntax.n  in
                        (match uu____17653 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17660 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____17660
                         | uu____17661 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____17665 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____17665 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____17670 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____17670 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17677 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17677
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____17680)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____17705 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____17705 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17712 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17712
                              | uu____17713 -> FStar_Pervasives_Native.None)
                         | uu____17716 -> FStar_Pervasives_Native.None)
                    | uu____17719 -> FStar_Pervasives_Native.None)
               | uu____17722 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17734 =
                 let uu____17735 = FStar_Syntax_Subst.compress phi  in
                 uu____17735.FStar_Syntax_Syntax.n  in
               match uu____17734 with
               | FStar_Syntax_Syntax.Tm_match (uu____17740,br::brs) ->
                   let uu____17807 = br  in
                   (match uu____17807 with
                    | (uu____17824,uu____17825,e) ->
                        let r =
                          let uu____17846 = simp_t e  in
                          match uu____17846 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17852 =
                                FStar_List.for_all
                                  (fun uu____17870  ->
                                     match uu____17870 with
                                     | (uu____17883,uu____17884,e') ->
                                         let uu____17898 = simp_t e'  in
                                         uu____17898 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17852
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17906 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17912 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17912
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17935 =
                 match uu____17935 with
                 | (t1,q) ->
                     let uu____17948 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17948 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17976 -> (t1, q))
                  in
               let uu____17985 = FStar_Syntax_Util.head_and_args t  in
               match uu____17985 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18048 =
                 let uu____18049 = FStar_Syntax_Util.unmeta ty  in
                 uu____18049.FStar_Syntax_Syntax.n  in
               match uu____18048 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18053) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18058,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18078 -> false  in
             let simplify1 arg =
               let uu____18102 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18102, arg)  in
             let uu____18111 = is_quantified_const tm1  in
             match uu____18111 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18115 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18115
             | FStar_Pervasives_Native.None  ->
                 let uu____18116 =
                   let uu____18117 = FStar_Syntax_Subst.compress tm1  in
                   uu____18117.FStar_Syntax_Syntax.n  in
                 (match uu____18116 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18121;
                              FStar_Syntax_Syntax.vars = uu____18122;_},uu____18123);
                         FStar_Syntax_Syntax.pos = uu____18124;
                         FStar_Syntax_Syntax.vars = uu____18125;_},args)
                      ->
                      let uu____18151 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18151
                      then
                        let uu____18152 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18152 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18199)::
                             (uu____18200,(arg,uu____18202))::[] ->
                             maybe_auto_squash arg
                         | (uu____18251,(arg,uu____18253))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18254)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18303)::uu____18304::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18355::(FStar_Pervasives_Native.Some (false
                                         ),uu____18356)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18407 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18421 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18421
                         then
                           let uu____18422 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18422 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18469)::uu____18470::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18521::(FStar_Pervasives_Native.Some (true
                                           ),uu____18522)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18573)::(uu____18574,(arg,uu____18576))::[]
                               -> maybe_auto_squash arg
                           | (uu____18625,(arg,uu____18627))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18628)::[]
                               -> maybe_auto_squash arg
                           | uu____18677 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18691 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18691
                            then
                              let uu____18692 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18692 with
                              | uu____18739::(FStar_Pervasives_Native.Some
                                              (true ),uu____18740)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18791)::uu____18792::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18843)::(uu____18844,(arg,uu____18846))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18895,(p,uu____18897))::(uu____18898,
                                                                (q,uu____18900))::[]
                                  ->
                                  let uu____18947 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18947
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18949 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18963 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18963
                               then
                                 let uu____18964 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18964 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19011)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19012)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19063)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19064)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19115)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19116)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19167)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19168)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19219,(arg,uu____19221))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19222)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19271)::(uu____19272,(arg,uu____19274))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19323,(arg,uu____19325))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19326)::[]
                                     ->
                                     let uu____19375 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19375
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19376)::(uu____19377,(arg,uu____19379))::[]
                                     ->
                                     let uu____19428 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19428
                                 | (uu____19429,(p,uu____19431))::(uu____19432,
                                                                   (q,uu____19434))::[]
                                     ->
                                     let uu____19481 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19481
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19483 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19497 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19497
                                  then
                                    let uu____19498 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19498 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19545)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19576)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19607 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19621 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19621
                                     then
                                       match args with
                                       | (t,uu____19623)::[] ->
                                           let uu____19640 =
                                             let uu____19641 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19641.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19640 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19644::[],body,uu____19646)
                                                ->
                                                let uu____19673 = simp_t body
                                                   in
                                                (match uu____19673 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19676 -> tm1)
                                            | uu____19679 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19681))::(t,uu____19683)::[]
                                           ->
                                           let uu____19722 =
                                             let uu____19723 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19723.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19722 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19726::[],body,uu____19728)
                                                ->
                                                let uu____19755 = simp_t body
                                                   in
                                                (match uu____19755 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19758 -> tm1)
                                            | uu____19761 -> tm1)
                                       | uu____19762 -> tm1
                                     else
                                       (let uu____19772 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19772
                                        then
                                          match args with
                                          | (t,uu____19774)::[] ->
                                              let uu____19791 =
                                                let uu____19792 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19792.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19791 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19795::[],body,uu____19797)
                                                   ->
                                                   let uu____19824 =
                                                     simp_t body  in
                                                   (match uu____19824 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19827 -> tm1)
                                               | uu____19830 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19832))::(t,uu____19834)::[]
                                              ->
                                              let uu____19873 =
                                                let uu____19874 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19874.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19873 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19877::[],body,uu____19879)
                                                   ->
                                                   let uu____19906 =
                                                     simp_t body  in
                                                   (match uu____19906 with
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
                                                    | uu____19909 -> tm1)
                                               | uu____19912 -> tm1)
                                          | uu____19913 -> tm1
                                        else
                                          (let uu____19923 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19923
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19924;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19925;_},uu____19926)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19943;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19944;_},uu____19945)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19962 -> tm1
                                           else
                                             (let uu____19972 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19972 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19992 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20002;
                         FStar_Syntax_Syntax.vars = uu____20003;_},args)
                      ->
                      let uu____20025 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20025
                      then
                        let uu____20026 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20026 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20073)::
                             (uu____20074,(arg,uu____20076))::[] ->
                             maybe_auto_squash arg
                         | (uu____20125,(arg,uu____20127))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20128)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20177)::uu____20178::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20229::(FStar_Pervasives_Native.Some (false
                                         ),uu____20230)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20281 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20295 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20295
                         then
                           let uu____20296 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20296 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20343)::uu____20344::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20395::(FStar_Pervasives_Native.Some (true
                                           ),uu____20396)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20447)::(uu____20448,(arg,uu____20450))::[]
                               -> maybe_auto_squash arg
                           | (uu____20499,(arg,uu____20501))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20502)::[]
                               -> maybe_auto_squash arg
                           | uu____20551 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20565 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20565
                            then
                              let uu____20566 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20566 with
                              | uu____20613::(FStar_Pervasives_Native.Some
                                              (true ),uu____20614)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20665)::uu____20666::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20717)::(uu____20718,(arg,uu____20720))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20769,(p,uu____20771))::(uu____20772,
                                                                (q,uu____20774))::[]
                                  ->
                                  let uu____20821 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20821
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20823 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20837 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20837
                               then
                                 let uu____20838 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20838 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20885)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20886)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20937)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20938)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20989)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20990)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21041)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21042)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21093,(arg,uu____21095))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21096)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21145)::(uu____21146,(arg,uu____21148))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21197,(arg,uu____21199))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21200)::[]
                                     ->
                                     let uu____21249 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21249
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21250)::(uu____21251,(arg,uu____21253))::[]
                                     ->
                                     let uu____21302 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21302
                                 | (uu____21303,(p,uu____21305))::(uu____21306,
                                                                   (q,uu____21308))::[]
                                     ->
                                     let uu____21355 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21355
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21357 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21371 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21371
                                  then
                                    let uu____21372 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21372 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21419)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21450)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21481 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21495 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21495
                                     then
                                       match args with
                                       | (t,uu____21497)::[] ->
                                           let uu____21514 =
                                             let uu____21515 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21515.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21514 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21518::[],body,uu____21520)
                                                ->
                                                let uu____21547 = simp_t body
                                                   in
                                                (match uu____21547 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21550 -> tm1)
                                            | uu____21553 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21555))::(t,uu____21557)::[]
                                           ->
                                           let uu____21596 =
                                             let uu____21597 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21597.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21596 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21600::[],body,uu____21602)
                                                ->
                                                let uu____21629 = simp_t body
                                                   in
                                                (match uu____21629 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21632 -> tm1)
                                            | uu____21635 -> tm1)
                                       | uu____21636 -> tm1
                                     else
                                       (let uu____21646 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21646
                                        then
                                          match args with
                                          | (t,uu____21648)::[] ->
                                              let uu____21665 =
                                                let uu____21666 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21666.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21665 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21669::[],body,uu____21671)
                                                   ->
                                                   let uu____21698 =
                                                     simp_t body  in
                                                   (match uu____21698 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21701 -> tm1)
                                               | uu____21704 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21706))::(t,uu____21708)::[]
                                              ->
                                              let uu____21747 =
                                                let uu____21748 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21748.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21747 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21751::[],body,uu____21753)
                                                   ->
                                                   let uu____21780 =
                                                     simp_t body  in
                                                   (match uu____21780 with
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
                                                    | uu____21783 -> tm1)
                                               | uu____21786 -> tm1)
                                          | uu____21787 -> tm1
                                        else
                                          (let uu____21797 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21797
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21798;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21799;_},uu____21800)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21817;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21818;_},uu____21819)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21836 -> tm1
                                           else
                                             (let uu____21846 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____21846 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____21866 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____21881 = simp_t t  in
                      (match uu____21881 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____21884 ->
                      let uu____21907 = is_const_match tm1  in
                      (match uu____21907 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____21910 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let uu____21915 =
            log cfg
              (fun uu____21920  ->
                 let uu____21921 =
                   let uu____21922 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____21923 = FStar_Syntax_Print.term_to_string t  in
                   let uu____21924 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____21931 =
                     let uu____21932 =
                       let uu____21935 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____21935
                        in
                     stack_to_string uu____21932  in
                   FStar_Util.print4
                     ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                     uu____21922 uu____21923 uu____21924 uu____21931
                    in
                 let uu____21958 =
                   FStar_TypeChecker_Env.debug cfg.tcenv
                     (FStar_Options.Other "NormRebuild")
                    in
                 if uu____21958
                 then
                   let uu____21959 = FStar_Syntax_Util.unbound_variables t
                      in
                   match uu____21959 with
                   | [] -> ()
                   | bvs ->
                       let uu____21965 =
                         let uu____21966 = FStar_Syntax_Print.tag_of_term t
                            in
                         let uu____21967 =
                           FStar_Syntax_Print.term_to_string t  in
                         let uu____21968 =
                           let uu____21969 =
                             FStar_All.pipe_right bvs
                               (FStar_List.map
                                  FStar_Syntax_Print.bv_to_string)
                              in
                           FStar_All.pipe_right uu____21969
                             (FStar_String.concat ", ")
                            in
                         FStar_Util.print3
                           "!!! Rebuild (%s) %s, free vars=%s\n" uu____21966
                           uu____21967 uu____21968
                          in
                       failwith "DIE!"
                 else ())
             in
          let t1 = maybe_simplify cfg env stack t  in
          match stack with
          | [] -> t1
          | (Debug (tm,time_then))::stack1 ->
              let uu____21985 =
                if (cfg.debug).print_normalized
                then
                  let time_now = FStar_Util.now ()  in
                  let uu____21987 =
                    let uu____21988 =
                      let uu____21989 =
                        FStar_Util.time_diff time_then time_now  in
                      FStar_Pervasives_Native.snd uu____21989  in
                    FStar_Util.string_of_int uu____21988  in
                  let uu____21994 = FStar_Syntax_Print.term_to_string tm  in
                  let uu____21995 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____21987 uu____21994 uu____21995
                else ()  in
              rebuild cfg env stack1 t1
          | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
          | (Meta (uu____22001,m,r))::stack1 ->
              let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
              rebuild cfg env stack1 t2
          | (MemoLazy r)::stack1 ->
              let uu____22020 = set_memo cfg r (env, t1)  in
              let uu____22047 =
                log cfg
                  (fun uu____22050  ->
                     let uu____22051 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22051)
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
              let uu____22087 =
                let uu___182_22088 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___182_22088.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___182_22088.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack1 uu____22087
          | (Arg (Univ uu____22089,uu____22090,uu____22091))::uu____22092 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____22095,uu____22096))::uu____22097 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack1 ->
              let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
              rebuild cfg env stack1 t2
          | (Arg (Clos (env_arg,tm,uu____22112,uu____22113),aq,r))::stack1
              when
              let uu____22163 = head_of t1  in
              FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22163 ->
              let t2 =
                let uu____22167 =
                  let uu____22170 =
                    let uu____22171 = closure_as_term cfg env_arg tm  in
                    (uu____22171, aq)  in
                  FStar_Syntax_Syntax.extend_app t1 uu____22170  in
                uu____22167 FStar_Pervasives_Native.None r  in
              rebuild cfg env stack1 t2
          | (Arg (Clos (env_arg,tm,m,uu____22177),aq,r))::stack1 ->
              let uu____22227 =
                log cfg
                  (fun uu____22230  ->
                     let uu____22231 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22231)
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
                (let uu____22241 = FStar_ST.op_Bang m  in
                 match uu____22241 with
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
                 | FStar_Pervasives_Native.Some (uu____22382,a) ->
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (a, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2)
          | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
              let t0 = t1  in
              let fallback msg uu____22431 =
                let uu____22432 =
                  log cfg
                    (fun uu____22435  ->
                       let uu____22436 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.print2 "Not reifying%s: %s\n" msg
                         uu____22436)
                   in
                let t2 =
                  FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                    FStar_Pervasives_Native.None r
                   in
                rebuild cfg env1 stack' t2  in
              let uu____22440 =
                let uu____22441 = FStar_Syntax_Subst.compress t1  in
                uu____22441.FStar_Syntax_Syntax.n  in
              (match uu____22440 with
               | FStar_Syntax_Syntax.Tm_meta
                   (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                   do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
               | FStar_Syntax_Syntax.Tm_meta
                   (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                   ->
                   let lifted =
                     let uu____22468 = closure_as_term cfg env1 ty  in
                     reify_lift cfg t2 msrc mtgt uu____22468  in
                   let uu____22469 =
                     log cfg
                       (fun uu____22472  ->
                          let uu____22473 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22473)
                      in
                   let uu____22474 = FStar_List.tl stack  in
                   norm cfg env1 uu____22474 lifted
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____22475);
                      FStar_Syntax_Syntax.pos = uu____22476;
                      FStar_Syntax_Syntax.vars = uu____22477;_},(e,uu____22479)::[])
                   -> norm cfg env1 stack' e
               | FStar_Syntax_Syntax.Tm_app uu____22508 when
                   (cfg.steps).primops ->
                   let uu____22523 = FStar_Syntax_Util.head_and_args t1  in
                   (match uu____22523 with
                    | (hd1,args) ->
                        let uu____22560 =
                          let uu____22561 = FStar_Syntax_Util.un_uinst hd1
                             in
                          uu____22561.FStar_Syntax_Syntax.n  in
                        (match uu____22560 with
                         | FStar_Syntax_Syntax.Tm_fvar fv ->
                             let uu____22565 = find_prim_step cfg fv  in
                             (match uu____22565 with
                              | FStar_Pervasives_Native.Some
                                  { name = uu____22568; arity = uu____22569;
                                    auto_reflect =
                                      FStar_Pervasives_Native.Some n1;
                                    strong_reduction_ok = uu____22571;
                                    requires_binder_substitution =
                                      uu____22572;
                                    interpretation = uu____22573;_}
                                  when (FStar_List.length args) = n1 ->
                                  norm cfg env1 stack' t1
                              | uu____22588 -> fallback " (3)" ())
                         | uu____22591 -> fallback " (4)" ()))
               | uu____22592 -> fallback " (2)" ())
          | (App (env1,head1,aq,r))::stack1 ->
              let t2 =
                FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                  FStar_Pervasives_Native.None r
                 in
              rebuild cfg env1 stack1 t2
          | (Match (env',branches,cfg1,r))::stack1 ->
              let uu____22610 =
                log cfg1
                  (fun uu____22613  ->
                     let uu____22614 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22614)
                 in
              let scrutinee_env = env  in
              let env1 = env'  in
              let scrutinee = t1  in
              let norm_and_rebuild_match uu____22622 =
                let uu____22623 =
                  log cfg1
                    (fun uu____22627  ->
                       let uu____22628 =
                         FStar_Syntax_Print.term_to_string scrutinee  in
                       let uu____22629 =
                         let uu____22630 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____22647  ->
                                   match uu____22647 with
                                   | (p,uu____22657,uu____22658) ->
                                       FStar_Syntax_Print.pat_to_string p))
                            in
                         FStar_All.pipe_right uu____22630
                           (FStar_String.concat "\n\t")
                          in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____22628 uu____22629)
                   in
                let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                let cfg_exclude_zeta =
                  let new_delta =
                    FStar_All.pipe_right cfg1.delta_level
                      (FStar_List.filter
                         (fun uu___91_22675  ->
                            match uu___91_22675 with
                            | FStar_TypeChecker_Env.Inlining  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | uu____22676 -> false))
                     in
                  let steps =
                    let uu___183_22678 = cfg1.steps  in
                    {
                      beta = (uu___183_22678.beta);
                      iota = (uu___183_22678.iota);
                      zeta = false;
                      weak = (uu___183_22678.weak);
                      hnf = (uu___183_22678.hnf);
                      primops = (uu___183_22678.primops);
                      do_not_unfold_pure_lets =
                        (uu___183_22678.do_not_unfold_pure_lets);
                      unfold_until = FStar_Pervasives_Native.None;
                      unfold_only = FStar_Pervasives_Native.None;
                      unfold_fully = (uu___183_22678.unfold_fully);
                      unfold_attr = FStar_Pervasives_Native.None;
                      unfold_tac = false;
                      pure_subterms_within_computations =
                        (uu___183_22678.pure_subterms_within_computations);
                      simplify = (uu___183_22678.simplify);
                      erase_universes = (uu___183_22678.erase_universes);
                      allow_unbound_universes =
                        (uu___183_22678.allow_unbound_universes);
                      reify_ = (uu___183_22678.reify_);
                      compress_uvars = (uu___183_22678.compress_uvars);
                      no_full_norm = (uu___183_22678.no_full_norm);
                      check_no_uvars = (uu___183_22678.check_no_uvars);
                      unmeta = (uu___183_22678.unmeta);
                      unascribe = (uu___183_22678.unascribe);
                      in_full_norm_request =
                        (uu___183_22678.in_full_norm_request)
                    }  in
                  let uu___184_22683 = cfg1  in
                  {
                    steps;
                    tcenv = (uu___184_22683.tcenv);
                    debug = (uu___184_22683.debug);
                    delta_level = new_delta;
                    primitive_steps = (uu___184_22683.primitive_steps);
                    strong = true;
                    memoize_lazy = (uu___184_22683.memoize_lazy);
                    normalize_pure_lets =
                      (uu___184_22683.normalize_pure_lets)
                  }  in
                let norm_or_whnf env2 t2 =
                  if whnf
                  then closure_as_term cfg_exclude_zeta env2 t2
                  else norm cfg_exclude_zeta env2 [] t2  in
                let rec norm_pat env2 p =
                  match p.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_constant uu____22719 -> (p, env2)
                  | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                      let uu____22740 =
                        FStar_All.pipe_right pats
                          (FStar_List.fold_left
                             (fun uu____22800  ->
                                fun uu____22801  ->
                                  match (uu____22800, uu____22801) with
                                  | ((pats1,env3),(p1,b)) ->
                                      let uu____22892 = norm_pat env3 p1  in
                                      (match uu____22892 with
                                       | (p2,env4) ->
                                           (((p2, b) :: pats1), env4)))
                             ([], env2))
                         in
                      (match uu____22740 with
                       | (pats1,env3) ->
                           ((let uu___185_22974 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_cons
                                    (fv, (FStar_List.rev pats1)));
                               FStar_Syntax_Syntax.p =
                                 (uu___185_22974.FStar_Syntax_Syntax.p)
                             }), env3))
                  | FStar_Syntax_Syntax.Pat_var x ->
                      let x1 =
                        let uu___186_22993 = x  in
                        let uu____22994 =
                          norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___186_22993.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___186_22993.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____22994
                        }  in
                      ((let uu___187_23008 = p  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var x1);
                          FStar_Syntax_Syntax.p =
                            (uu___187_23008.FStar_Syntax_Syntax.p)
                        }), (dummy :: env2))
                  | FStar_Syntax_Syntax.Pat_wild x ->
                      let x1 =
                        let uu___188_23019 = x  in
                        let uu____23020 =
                          norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___188_23019.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___188_23019.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____23020
                        }  in
                      ((let uu___189_23034 = p  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild x1);
                          FStar_Syntax_Syntax.p =
                            (uu___189_23034.FStar_Syntax_Syntax.p)
                        }), (dummy :: env2))
                  | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                      let x1 =
                        let uu___190_23050 = x  in
                        let uu____23051 =
                          norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___190_23050.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___190_23050.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____23051
                        }  in
                      let t3 = norm_or_whnf env2 t2  in
                      ((let uu___191_23058 = p  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                          FStar_Syntax_Syntax.p =
                            (uu___191_23058.FStar_Syntax_Syntax.p)
                        }), env2)
                   in
                let branches1 =
                  match env1 with
                  | [] when whnf -> branches
                  | uu____23068 ->
                      FStar_All.pipe_right branches
                        (FStar_List.map
                           (fun branch1  ->
                              let uu____23082 =
                                FStar_Syntax_Subst.open_branch branch1  in
                              match uu____23082 with
                              | (p,wopt,e) ->
                                  let uu____23102 = norm_pat env1 p  in
                                  (match uu____23102 with
                                   | (p1,env2) ->
                                       let wopt1 =
                                         match wopt with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____23127 =
                                               norm_or_whnf env2 w  in
                                             FStar_Pervasives_Native.Some
                                               uu____23127
                                          in
                                       let e1 = norm_or_whnf env2 e  in
                                       FStar_Syntax_Util.branch
                                         (p1, wopt1, e1))))
                   in
                let scrutinee1 =
                  let uu____23134 =
                    (((cfg1.steps).iota &&
                        (Prims.op_Negation (cfg1.steps).weak))
                       && (Prims.op_Negation (cfg1.steps).compress_uvars))
                      && (maybe_weakly_reduced scrutinee)
                     in
                  if uu____23134
                  then norm cfg1 scrutinee_env [] scrutinee
                  else scrutinee  in
                let uu____23136 =
                  mk (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1)) r
                   in
                rebuild cfg1 env1 stack1 uu____23136  in
              let rec is_cons head1 =
                let uu____23142 =
                  let uu____23143 = FStar_Syntax_Subst.compress head1  in
                  uu____23143.FStar_Syntax_Syntax.n  in
                match uu____23142 with
                | FStar_Syntax_Syntax.Tm_uinst (h,uu____23147) -> is_cons h
                | FStar_Syntax_Syntax.Tm_constant uu____23152 -> true
                | FStar_Syntax_Syntax.Tm_fvar
                    { FStar_Syntax_Syntax.fv_name = uu____23153;
                      FStar_Syntax_Syntax.fv_delta = uu____23154;
                      FStar_Syntax_Syntax.fv_qual =
                        FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Data_ctor );_}
                    -> true
                | FStar_Syntax_Syntax.Tm_fvar
                    { FStar_Syntax_Syntax.fv_name = uu____23155;
                      FStar_Syntax_Syntax.fv_delta = uu____23156;
                      FStar_Syntax_Syntax.fv_qual =
                        FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_ctor uu____23157);_}
                    -> true
                | uu____23164 -> false  in
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
                let uu____23317 = FStar_Syntax_Util.head_and_args scrutinee1
                   in
                match uu____23317 with
                | (head1,args) ->
                    (match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_var bv ->
                         FStar_Util.Inl [(bv, scrutinee_orig)]
                     | FStar_Syntax_Syntax.Pat_wild bv ->
                         FStar_Util.Inl [(bv, scrutinee_orig)]
                     | FStar_Syntax_Syntax.Pat_dot_term uu____23404 ->
                         FStar_Util.Inl []
                     | FStar_Syntax_Syntax.Pat_constant s ->
                         (match scrutinee1.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_constant s' when
                              FStar_Const.eq_const s s' -> FStar_Util.Inl []
                          | uu____23443 ->
                              let uu____23444 =
                                let uu____23445 = is_cons head1  in
                                Prims.op_Negation uu____23445  in
                              FStar_Util.Inr uu____23444)
                     | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                         let uu____23470 =
                           let uu____23471 = FStar_Syntax_Util.un_uinst head1
                              in
                           uu____23471.FStar_Syntax_Syntax.n  in
                         (match uu____23470 with
                          | FStar_Syntax_Syntax.Tm_fvar fv' when
                              FStar_Syntax_Syntax.fv_eq fv fv' ->
                              matches_args [] args arg_pats
                          | uu____23489 ->
                              let uu____23490 =
                                let uu____23491 = is_cons head1  in
                                Prims.op_Negation uu____23491  in
                              FStar_Util.Inr uu____23490))
              
              and matches_args out a p =
                match (a, p) with
                | ([],[]) -> FStar_Util.Inl out
                | ((t2,uu____23560)::rest_a,(p1,uu____23563)::rest_p) ->
                    let uu____23607 = matches_pat t2 p1  in
                    (match uu____23607 with
                     | FStar_Util.Inl s ->
                         matches_args (FStar_List.append out s) rest_a rest_p
                     | m -> m)
                | uu____23656 -> FStar_Util.Inr false
               in
              let rec matches scrutinee1 p =
                match p with
                | [] -> norm_and_rebuild_match ()
                | (p1,wopt,b)::rest ->
                    let uu____23764 = matches_pat scrutinee1 p1  in
                    (match uu____23764 with
                     | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                     | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                     | FStar_Util.Inl s ->
                         let uu____23800 =
                           log cfg1
                             (fun uu____23804  ->
                                let uu____23805 =
                                  FStar_Syntax_Print.pat_to_string p1  in
                                let uu____23806 =
                                  let uu____23807 =
                                    FStar_List.map
                                      (fun uu____23817  ->
                                         match uu____23817 with
                                         | (uu____23822,t2) ->
                                             FStar_Syntax_Print.term_to_string
                                               t2) s
                                     in
                                  FStar_All.pipe_right uu____23807
                                    (FStar_String.concat "; ")
                                   in
                                FStar_Util.print2
                                  "Matches pattern %s with subst = %s\n"
                                  uu____23805 uu____23806)
                            in
                         let env0 = env1  in
                         let env2 =
                           FStar_List.fold_left
                             (fun env2  ->
                                fun uu____23854  ->
                                  match uu____23854 with
                                  | (bv,t2) ->
                                      let uu____23877 =
                                        let uu____23884 =
                                          let uu____23887 =
                                            FStar_Syntax_Syntax.mk_binder bv
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____23887
                                           in
                                        let uu____23888 =
                                          let uu____23889 =
                                            let uu____23920 =
                                              FStar_Util.mk_ref
                                                (FStar_Pervasives_Native.Some
                                                   ([], t2))
                                               in
                                            ([], t2, uu____23920, false)  in
                                          Clos uu____23889  in
                                        (uu____23884, uu____23888)  in
                                      uu____23877 :: env2) env1 s
                            in
                         let uu____24037 = guard_when_clause wopt b rest  in
                         norm cfg1 env2 stack1 uu____24037)
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
    let uu____24063 =
      let uu____24066 = FStar_ST.op_Bang plugins  in p :: uu____24066  in
    FStar_ST.op_Colon_Equals plugins uu____24063  in
  let retrieve uu____24173 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24250  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_24291  ->
                  match uu___92_24291 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24295 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24301 -> d  in
        let uu____24304 = to_fsteps s  in
        let uu____24305 =
          let uu____24306 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24307 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24308 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24309 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24310 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24306;
            primop = uu____24307;
            b380 = uu____24308;
            norm_delayed = uu____24309;
            print_normalized = uu____24310
          }  in
        let uu____24311 =
          let uu____24314 =
            let uu____24317 = retrieve_plugins ()  in
            FStar_List.append uu____24317 psteps  in
          add_steps built_in_primitive_steps uu____24314  in
        let uu____24320 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24322 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24322)
           in
        {
          steps = uu____24304;
          tcenv = e;
          debug = uu____24305;
          delta_level = d1;
          primitive_steps = uu____24311;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24320
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
      fun t  -> let uu____24404 = config s e  in norm_comp uu____24404 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24421 = config [] env  in norm_universe uu____24421 [] u
  
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
        let uu____24444 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24444  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24451 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___192_24470 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___192_24470.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___192_24470.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24477 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24477
          then
            let ct1 =
              let uu____24479 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24479 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24486 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24486
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___193_24490 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___193_24490.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___193_24490.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___193_24490.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___194_24492 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___194_24492.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___194_24492.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___194_24492.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___194_24492.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___195_24493 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___195_24493.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_24493.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24495 -> c
  
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
        let uu____24512 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24512  in
      let uu____24519 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24519
      then
        let uu____24520 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24520 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24526  ->
                 let uu____24527 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24527)
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
            let uu____24547 =
              let uu____24548 =
                let uu____24553 =
                  let uu____24554 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24554
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24553)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24548
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
          let uu____24569 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24569 [] c
        with
        | e ->
            let uu____24581 =
              let uu____24582 =
                let uu____24587 =
                  let uu____24588 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24588
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24587)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24582
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
                   let uu____24632 =
                     let uu____24633 =
                       let uu____24640 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24640)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24633  in
                   mk uu____24632 t01.FStar_Syntax_Syntax.pos
               | uu____24645 -> t2)
          | uu____24646 -> t2  in
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
        let uu____24710 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____24710 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____24739 ->
                 let uu____24746 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____24746 with
                  | (actuals,uu____24756,uu____24757) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____24771 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____24771 with
                         | (binders,args) ->
                             let uu____24788 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____24788
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
      | uu____24800 ->
          let uu____24801 = FStar_Syntax_Util.head_and_args t  in
          (match uu____24801 with
           | (head1,args) ->
               let uu____24838 =
                 let uu____24839 = FStar_Syntax_Subst.compress head1  in
                 uu____24839.FStar_Syntax_Syntax.n  in
               (match uu____24838 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____24842,thead) ->
                    let uu____24868 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____24868 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____24910 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_24918 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_24918.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_24918.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_24918.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_24918.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_24918.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_24918.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_24918.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_24918.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_24918.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_24918.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_24918.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_24918.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_24918.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_24918.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_24918.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_24918.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_24918.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_24918.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___200_24918.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___200_24918.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___200_24918.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_24918.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_24918.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___200_24918.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___200_24918.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___200_24918.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___200_24918.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___200_24918.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___200_24918.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___200_24918.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___200_24918.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___200_24918.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___200_24918.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___200_24918.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____24910 with
                            | (uu____24919,ty,uu____24921) ->
                                eta_expand_with_type env t ty))
                | uu____24922 ->
                    let uu____24923 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_24931 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_24931.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_24931.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_24931.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_24931.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_24931.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_24931.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_24931.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_24931.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_24931.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_24931.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_24931.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_24931.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_24931.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_24931.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_24931.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_24931.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_24931.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_24931.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___201_24931.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___201_24931.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___201_24931.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_24931.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_24931.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___201_24931.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___201_24931.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___201_24931.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___201_24931.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___201_24931.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___201_24931.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___201_24931.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___201_24931.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___201_24931.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___201_24931.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___201_24931.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____24923 with
                     | (uu____24932,ty,uu____24934) ->
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
      let uu___202_25005 = x  in
      let uu____25006 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___202_25005.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___202_25005.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25006
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25009 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25034 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25035 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25036 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25037 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25044 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25045 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25046 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___203_25075 = rc  in
          let uu____25076 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25083 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___203_25075.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25076;
            FStar_Syntax_Syntax.residual_flags = uu____25083
          }  in
        let uu____25086 =
          let uu____25087 =
            let uu____25104 = elim_delayed_subst_binders bs  in
            let uu____25111 = elim_delayed_subst_term t2  in
            let uu____25112 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25104, uu____25111, uu____25112)  in
          FStar_Syntax_Syntax.Tm_abs uu____25087  in
        mk1 uu____25086
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25141 =
          let uu____25142 =
            let uu____25155 = elim_delayed_subst_binders bs  in
            let uu____25162 = elim_delayed_subst_comp c  in
            (uu____25155, uu____25162)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25142  in
        mk1 uu____25141
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25175 =
          let uu____25176 =
            let uu____25183 = elim_bv bv  in
            let uu____25184 = elim_delayed_subst_term phi  in
            (uu____25183, uu____25184)  in
          FStar_Syntax_Syntax.Tm_refine uu____25176  in
        mk1 uu____25175
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25207 =
          let uu____25208 =
            let uu____25223 = elim_delayed_subst_term t2  in
            let uu____25224 = elim_delayed_subst_args args  in
            (uu____25223, uu____25224)  in
          FStar_Syntax_Syntax.Tm_app uu____25208  in
        mk1 uu____25207
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___204_25289 = p  in
              let uu____25290 =
                let uu____25291 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25291  in
              {
                FStar_Syntax_Syntax.v = uu____25290;
                FStar_Syntax_Syntax.p =
                  (uu___204_25289.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___205_25293 = p  in
              let uu____25294 =
                let uu____25295 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25295  in
              {
                FStar_Syntax_Syntax.v = uu____25294;
                FStar_Syntax_Syntax.p =
                  (uu___205_25293.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___206_25302 = p  in
              let uu____25303 =
                let uu____25304 =
                  let uu____25311 = elim_bv x  in
                  let uu____25312 = elim_delayed_subst_term t0  in
                  (uu____25311, uu____25312)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25304  in
              {
                FStar_Syntax_Syntax.v = uu____25303;
                FStar_Syntax_Syntax.p =
                  (uu___206_25302.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___207_25331 = p  in
              let uu____25332 =
                let uu____25333 =
                  let uu____25346 =
                    FStar_List.map
                      (fun uu____25369  ->
                         match uu____25369 with
                         | (x,b) ->
                             let uu____25382 = elim_pat x  in
                             (uu____25382, b)) pats
                     in
                  (fv, uu____25346)  in
                FStar_Syntax_Syntax.Pat_cons uu____25333  in
              {
                FStar_Syntax_Syntax.v = uu____25332;
                FStar_Syntax_Syntax.p =
                  (uu___207_25331.FStar_Syntax_Syntax.p)
              }
          | uu____25395 -> p  in
        let elim_branch uu____25418 =
          match uu____25418 with
          | (pat,wopt,t3) ->
              let uu____25444 = elim_pat pat  in
              let uu____25447 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25450 = elim_delayed_subst_term t3  in
              (uu____25444, uu____25447, uu____25450)
           in
        let uu____25455 =
          let uu____25456 =
            let uu____25479 = elim_delayed_subst_term t2  in
            let uu____25480 = FStar_List.map elim_branch branches  in
            (uu____25479, uu____25480)  in
          FStar_Syntax_Syntax.Tm_match uu____25456  in
        mk1 uu____25455
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25590 =
          match uu____25590 with
          | (tc,topt) ->
              let uu____25625 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25635 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25635
                | FStar_Util.Inr c ->
                    let uu____25637 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25637
                 in
              let uu____25638 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25625, uu____25638)
           in
        let uu____25647 =
          let uu____25648 =
            let uu____25675 = elim_delayed_subst_term t2  in
            let uu____25676 = elim_ascription a  in
            (uu____25675, uu____25676, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____25648  in
        mk1 uu____25647
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___208_25722 = lb  in
          let uu____25723 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____25726 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___208_25722.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___208_25722.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____25723;
            FStar_Syntax_Syntax.lbeff =
              (uu___208_25722.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____25726;
            FStar_Syntax_Syntax.lbattrs =
              (uu___208_25722.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___208_25722.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____25729 =
          let uu____25730 =
            let uu____25743 =
              let uu____25750 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____25750)  in
            let uu____25759 = elim_delayed_subst_term t2  in
            (uu____25743, uu____25759)  in
          FStar_Syntax_Syntax.Tm_let uu____25730  in
        mk1 uu____25729
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____25792 =
          let uu____25793 =
            let uu____25810 = elim_delayed_subst_term t2  in
            (uv, uu____25810)  in
          FStar_Syntax_Syntax.Tm_uvar uu____25793  in
        mk1 uu____25792
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____25828 =
          let uu____25829 =
            let uu____25836 = elim_delayed_subst_term tm  in
            (uu____25836, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____25829  in
        mk1 uu____25828
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____25843 =
          let uu____25844 =
            let uu____25851 = elim_delayed_subst_term t2  in
            let uu____25852 = elim_delayed_subst_meta md  in
            (uu____25851, uu____25852)  in
          FStar_Syntax_Syntax.Tm_meta uu____25844  in
        mk1 uu____25843

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_25859  ->
         match uu___93_25859 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____25863 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____25863
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
        let uu____25885 =
          let uu____25886 =
            let uu____25895 = elim_delayed_subst_term t  in
            (uu____25895, uopt)  in
          FStar_Syntax_Syntax.Total uu____25886  in
        mk1 uu____25885
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____25908 =
          let uu____25909 =
            let uu____25918 = elim_delayed_subst_term t  in
            (uu____25918, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____25909  in
        mk1 uu____25908
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___209_25923 = ct  in
          let uu____25924 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____25927 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____25936 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___209_25923.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___209_25923.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____25924;
            FStar_Syntax_Syntax.effect_args = uu____25927;
            FStar_Syntax_Syntax.flags = uu____25936
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_25939  ->
    match uu___94_25939 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____25951 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____25951
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____25984 =
          let uu____25991 = elim_delayed_subst_term t  in (m, uu____25991)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____25984
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____25999 =
          let uu____26008 = elim_delayed_subst_term t  in
          (m1, m2, uu____26008)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____25999
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26031  ->
         match uu____26031 with
         | (t,q) ->
             let uu____26042 = elim_delayed_subst_term t  in (uu____26042, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26062  ->
         match uu____26062 with
         | (x,q) ->
             let uu____26073 =
               let uu___210_26074 = x  in
               let uu____26075 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___210_26074.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___210_26074.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26075
               }  in
             (uu____26073, q)) bs

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
            | (uu____26159,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26165,FStar_Util.Inl t) ->
                let uu____26171 =
                  let uu____26176 =
                    let uu____26177 =
                      let uu____26190 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26190)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26177  in
                  FStar_Syntax_Syntax.mk uu____26176  in
                uu____26171 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26194 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26194 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26222 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26277 ->
                    let uu____26278 =
                      let uu____26287 =
                        let uu____26288 = FStar_Syntax_Subst.compress t4  in
                        uu____26288.FStar_Syntax_Syntax.n  in
                      (uu____26287, tc)  in
                    (match uu____26278 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26313) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26350) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26389,FStar_Util.Inl uu____26390) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26413 -> failwith "Impossible")
                 in
              (match uu____26222 with
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
          let uu____26526 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26526 with
          | (univ_names1,binders1,tc) ->
              let uu____26584 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26584)
  
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
          let uu____26627 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26627 with
          | (univ_names1,binders1,tc) ->
              let uu____26687 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____26687)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____26724 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____26724 with
           | (univ_names1,binders1,typ1) ->
               let uu___211_26752 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_26752.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_26752.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_26752.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_26752.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___212_26773 = s  in
          let uu____26774 =
            let uu____26775 =
              let uu____26784 = FStar_List.map (elim_uvars env) sigs  in
              (uu____26784, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____26775  in
          {
            FStar_Syntax_Syntax.sigel = uu____26774;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_26773.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_26773.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_26773.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_26773.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____26801 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____26801 with
           | (univ_names1,uu____26819,typ1) ->
               let uu___213_26833 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_26833.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_26833.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_26833.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_26833.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____26839 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____26839 with
           | (univ_names1,uu____26857,typ1) ->
               let uu___214_26871 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_26871.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_26871.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_26871.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_26871.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26905 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26905 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26929 =
                            let uu____26930 =
                              let uu____26931 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26931  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26930
                             in
                          elim_delayed_subst_term uu____26929  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___215_26934 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___215_26934.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_26934.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___215_26934.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___215_26934.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___216_26935 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___216_26935.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_26935.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_26935.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_26935.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___217_26947 = s  in
          let uu____26948 =
            let uu____26949 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26949  in
          {
            FStar_Syntax_Syntax.sigel = uu____26948;
            FStar_Syntax_Syntax.sigrng =
              (uu___217_26947.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_26947.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_26947.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_26947.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26953 = elim_uvars_aux_t env us [] t  in
          (match uu____26953 with
           | (us1,uu____26971,t1) ->
               let uu___218_26985 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_26985.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_26985.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_26985.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_26985.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26986 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26988 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26988 with
           | (univs1,binders,signature) ->
               let uu____27016 =
                 let uu____27025 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27025 with
                 | (univs_opening,univs2) ->
                     let uu____27052 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27052)
                  in
               (match uu____27016 with
                | (univs_opening,univs_closing) ->
                    let uu____27069 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27075 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27076 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27075, uu____27076)  in
                    (match uu____27069 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27099 =
                           match uu____27099 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27117 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27117 with
                                | (us1,t1) ->
                                    let uu____27128 =
                                      let uu____27133 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27140 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27133, uu____27140)  in
                                    (match uu____27128 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27153 =
                                           let uu____27158 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27167 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27158, uu____27167)  in
                                         (match uu____27153 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27183 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27183
                                                 in
                                              let uu____27184 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27184 with
                                               | (uu____27205,uu____27206,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27221 =
                                                       let uu____27222 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27222
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27221
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27228 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27228 with
                           | (uu____27241,uu____27242,t1) -> t1  in
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
                             | uu____27303 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27321 =
                               let uu____27322 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27322.FStar_Syntax_Syntax.n  in
                             match uu____27321 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27381 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27411 =
                               let uu____27412 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27412.FStar_Syntax_Syntax.n  in
                             match uu____27411 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27433) ->
                                 let uu____27454 = destruct_action_body body
                                    in
                                 (match uu____27454 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27499 ->
                                 let uu____27500 = destruct_action_body t  in
                                 (match uu____27500 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27549 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27549 with
                           | (action_univs,t) ->
                               let uu____27558 = destruct_action_typ_templ t
                                  in
                               (match uu____27558 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___219_27599 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___219_27599.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___219_27599.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___220_27601 = ed  in
                           let uu____27602 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27603 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27604 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27605 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27606 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27607 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27608 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27609 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27610 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27611 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27612 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27613 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27614 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27615 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___220_27601.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___220_27601.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27602;
                             FStar_Syntax_Syntax.bind_wp = uu____27603;
                             FStar_Syntax_Syntax.if_then_else = uu____27604;
                             FStar_Syntax_Syntax.ite_wp = uu____27605;
                             FStar_Syntax_Syntax.stronger = uu____27606;
                             FStar_Syntax_Syntax.close_wp = uu____27607;
                             FStar_Syntax_Syntax.assert_p = uu____27608;
                             FStar_Syntax_Syntax.assume_p = uu____27609;
                             FStar_Syntax_Syntax.null_wp = uu____27610;
                             FStar_Syntax_Syntax.trivial = uu____27611;
                             FStar_Syntax_Syntax.repr = uu____27612;
                             FStar_Syntax_Syntax.return_repr = uu____27613;
                             FStar_Syntax_Syntax.bind_repr = uu____27614;
                             FStar_Syntax_Syntax.actions = uu____27615;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___220_27601.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___221_27618 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___221_27618.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___221_27618.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___221_27618.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___221_27618.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_27636 =
            match uu___95_27636 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____27663 = elim_uvars_aux_t env us [] t  in
                (match uu____27663 with
                 | (us1,uu____27687,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___222_27706 = sub_eff  in
            let uu____27707 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27710 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___222_27706.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___222_27706.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27707;
              FStar_Syntax_Syntax.lift = uu____27710
            }  in
          let uu___223_27713 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___223_27713.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_27713.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_27713.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_27713.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27723 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27723 with
           | (univ_names1,binders1,comp1) ->
               let uu___224_27757 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_27757.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_27757.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_27757.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_27757.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27768 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27769 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  