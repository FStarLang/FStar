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
  fun projectee  -> match projectee with | Beta  -> true | uu____28 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____32 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____36 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____41 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____52 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____56 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____60 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____64 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____72 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____77 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____91 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____111 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____129 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____140 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____144 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____148 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____152 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____156 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____160 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____164 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____168 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____172 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____176 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____180 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____188 'Auu____189 .
    ('Auu____188 -> 'Auu____189) ->
      'Auu____189 ->
        'Auu____188 FStar_Pervasives_Native.option -> 'Auu____189
  =
  fun f  ->
    fun d  ->
      fun uu___77_206  ->
        match uu___77_206 with
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
      let add_opt x uu___78_1292 =
        match uu___78_1292 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1312 = fs  in
          {
            beta = true;
            iota = (uu___96_1312.iota);
            zeta = (uu___96_1312.zeta);
            weak = (uu___96_1312.weak);
            hnf = (uu___96_1312.hnf);
            primops = (uu___96_1312.primops);
            do_not_unfold_pure_lets = (uu___96_1312.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1312.unfold_until);
            unfold_only = (uu___96_1312.unfold_only);
            unfold_fully = (uu___96_1312.unfold_fully);
            unfold_attr = (uu___96_1312.unfold_attr);
            unfold_tac = (uu___96_1312.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1312.pure_subterms_within_computations);
            simplify = (uu___96_1312.simplify);
            erase_universes = (uu___96_1312.erase_universes);
            allow_unbound_universes = (uu___96_1312.allow_unbound_universes);
            reify_ = (uu___96_1312.reify_);
            compress_uvars = (uu___96_1312.compress_uvars);
            no_full_norm = (uu___96_1312.no_full_norm);
            check_no_uvars = (uu___96_1312.check_no_uvars);
            unmeta = (uu___96_1312.unmeta);
            unascribe = (uu___96_1312.unascribe);
            in_full_norm_request = (uu___96_1312.in_full_norm_request)
          }
      | Iota  ->
          let uu___97_1313 = fs  in
          {
            beta = (uu___97_1313.beta);
            iota = true;
            zeta = (uu___97_1313.zeta);
            weak = (uu___97_1313.weak);
            hnf = (uu___97_1313.hnf);
            primops = (uu___97_1313.primops);
            do_not_unfold_pure_lets = (uu___97_1313.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1313.unfold_until);
            unfold_only = (uu___97_1313.unfold_only);
            unfold_fully = (uu___97_1313.unfold_fully);
            unfold_attr = (uu___97_1313.unfold_attr);
            unfold_tac = (uu___97_1313.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1313.pure_subterms_within_computations);
            simplify = (uu___97_1313.simplify);
            erase_universes = (uu___97_1313.erase_universes);
            allow_unbound_universes = (uu___97_1313.allow_unbound_universes);
            reify_ = (uu___97_1313.reify_);
            compress_uvars = (uu___97_1313.compress_uvars);
            no_full_norm = (uu___97_1313.no_full_norm);
            check_no_uvars = (uu___97_1313.check_no_uvars);
            unmeta = (uu___97_1313.unmeta);
            unascribe = (uu___97_1313.unascribe);
            in_full_norm_request = (uu___97_1313.in_full_norm_request)
          }
      | Zeta  ->
          let uu___98_1314 = fs  in
          {
            beta = (uu___98_1314.beta);
            iota = (uu___98_1314.iota);
            zeta = true;
            weak = (uu___98_1314.weak);
            hnf = (uu___98_1314.hnf);
            primops = (uu___98_1314.primops);
            do_not_unfold_pure_lets = (uu___98_1314.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1314.unfold_until);
            unfold_only = (uu___98_1314.unfold_only);
            unfold_fully = (uu___98_1314.unfold_fully);
            unfold_attr = (uu___98_1314.unfold_attr);
            unfold_tac = (uu___98_1314.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1314.pure_subterms_within_computations);
            simplify = (uu___98_1314.simplify);
            erase_universes = (uu___98_1314.erase_universes);
            allow_unbound_universes = (uu___98_1314.allow_unbound_universes);
            reify_ = (uu___98_1314.reify_);
            compress_uvars = (uu___98_1314.compress_uvars);
            no_full_norm = (uu___98_1314.no_full_norm);
            check_no_uvars = (uu___98_1314.check_no_uvars);
            unmeta = (uu___98_1314.unmeta);
            unascribe = (uu___98_1314.unascribe);
            in_full_norm_request = (uu___98_1314.in_full_norm_request)
          }
      | Exclude (Beta ) ->
          let uu___99_1315 = fs  in
          {
            beta = false;
            iota = (uu___99_1315.iota);
            zeta = (uu___99_1315.zeta);
            weak = (uu___99_1315.weak);
            hnf = (uu___99_1315.hnf);
            primops = (uu___99_1315.primops);
            do_not_unfold_pure_lets = (uu___99_1315.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1315.unfold_until);
            unfold_only = (uu___99_1315.unfold_only);
            unfold_fully = (uu___99_1315.unfold_fully);
            unfold_attr = (uu___99_1315.unfold_attr);
            unfold_tac = (uu___99_1315.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1315.pure_subterms_within_computations);
            simplify = (uu___99_1315.simplify);
            erase_universes = (uu___99_1315.erase_universes);
            allow_unbound_universes = (uu___99_1315.allow_unbound_universes);
            reify_ = (uu___99_1315.reify_);
            compress_uvars = (uu___99_1315.compress_uvars);
            no_full_norm = (uu___99_1315.no_full_norm);
            check_no_uvars = (uu___99_1315.check_no_uvars);
            unmeta = (uu___99_1315.unmeta);
            unascribe = (uu___99_1315.unascribe);
            in_full_norm_request = (uu___99_1315.in_full_norm_request)
          }
      | Exclude (Iota ) ->
          let uu___100_1316 = fs  in
          {
            beta = (uu___100_1316.beta);
            iota = false;
            zeta = (uu___100_1316.zeta);
            weak = (uu___100_1316.weak);
            hnf = (uu___100_1316.hnf);
            primops = (uu___100_1316.primops);
            do_not_unfold_pure_lets = (uu___100_1316.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1316.unfold_until);
            unfold_only = (uu___100_1316.unfold_only);
            unfold_fully = (uu___100_1316.unfold_fully);
            unfold_attr = (uu___100_1316.unfold_attr);
            unfold_tac = (uu___100_1316.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1316.pure_subterms_within_computations);
            simplify = (uu___100_1316.simplify);
            erase_universes = (uu___100_1316.erase_universes);
            allow_unbound_universes = (uu___100_1316.allow_unbound_universes);
            reify_ = (uu___100_1316.reify_);
            compress_uvars = (uu___100_1316.compress_uvars);
            no_full_norm = (uu___100_1316.no_full_norm);
            check_no_uvars = (uu___100_1316.check_no_uvars);
            unmeta = (uu___100_1316.unmeta);
            unascribe = (uu___100_1316.unascribe);
            in_full_norm_request = (uu___100_1316.in_full_norm_request)
          }
      | Exclude (Zeta ) ->
          let uu___101_1317 = fs  in
          {
            beta = (uu___101_1317.beta);
            iota = (uu___101_1317.iota);
            zeta = false;
            weak = (uu___101_1317.weak);
            hnf = (uu___101_1317.hnf);
            primops = (uu___101_1317.primops);
            do_not_unfold_pure_lets = (uu___101_1317.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1317.unfold_until);
            unfold_only = (uu___101_1317.unfold_only);
            unfold_fully = (uu___101_1317.unfold_fully);
            unfold_attr = (uu___101_1317.unfold_attr);
            unfold_tac = (uu___101_1317.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1317.pure_subterms_within_computations);
            simplify = (uu___101_1317.simplify);
            erase_universes = (uu___101_1317.erase_universes);
            allow_unbound_universes = (uu___101_1317.allow_unbound_universes);
            reify_ = (uu___101_1317.reify_);
            compress_uvars = (uu___101_1317.compress_uvars);
            no_full_norm = (uu___101_1317.no_full_norm);
            check_no_uvars = (uu___101_1317.check_no_uvars);
            unmeta = (uu___101_1317.unmeta);
            unascribe = (uu___101_1317.unascribe);
            in_full_norm_request = (uu___101_1317.in_full_norm_request)
          }
      | Exclude uu____1318 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1319 = fs  in
          {
            beta = (uu___102_1319.beta);
            iota = (uu___102_1319.iota);
            zeta = (uu___102_1319.zeta);
            weak = true;
            hnf = (uu___102_1319.hnf);
            primops = (uu___102_1319.primops);
            do_not_unfold_pure_lets = (uu___102_1319.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1319.unfold_until);
            unfold_only = (uu___102_1319.unfold_only);
            unfold_fully = (uu___102_1319.unfold_fully);
            unfold_attr = (uu___102_1319.unfold_attr);
            unfold_tac = (uu___102_1319.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1319.pure_subterms_within_computations);
            simplify = (uu___102_1319.simplify);
            erase_universes = (uu___102_1319.erase_universes);
            allow_unbound_universes = (uu___102_1319.allow_unbound_universes);
            reify_ = (uu___102_1319.reify_);
            compress_uvars = (uu___102_1319.compress_uvars);
            no_full_norm = (uu___102_1319.no_full_norm);
            check_no_uvars = (uu___102_1319.check_no_uvars);
            unmeta = (uu___102_1319.unmeta);
            unascribe = (uu___102_1319.unascribe);
            in_full_norm_request = (uu___102_1319.in_full_norm_request)
          }
      | HNF  ->
          let uu___103_1320 = fs  in
          {
            beta = (uu___103_1320.beta);
            iota = (uu___103_1320.iota);
            zeta = (uu___103_1320.zeta);
            weak = (uu___103_1320.weak);
            hnf = true;
            primops = (uu___103_1320.primops);
            do_not_unfold_pure_lets = (uu___103_1320.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1320.unfold_until);
            unfold_only = (uu___103_1320.unfold_only);
            unfold_fully = (uu___103_1320.unfold_fully);
            unfold_attr = (uu___103_1320.unfold_attr);
            unfold_tac = (uu___103_1320.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1320.pure_subterms_within_computations);
            simplify = (uu___103_1320.simplify);
            erase_universes = (uu___103_1320.erase_universes);
            allow_unbound_universes = (uu___103_1320.allow_unbound_universes);
            reify_ = (uu___103_1320.reify_);
            compress_uvars = (uu___103_1320.compress_uvars);
            no_full_norm = (uu___103_1320.no_full_norm);
            check_no_uvars = (uu___103_1320.check_no_uvars);
            unmeta = (uu___103_1320.unmeta);
            unascribe = (uu___103_1320.unascribe);
            in_full_norm_request = (uu___103_1320.in_full_norm_request)
          }
      | Primops  ->
          let uu___104_1321 = fs  in
          {
            beta = (uu___104_1321.beta);
            iota = (uu___104_1321.iota);
            zeta = (uu___104_1321.zeta);
            weak = (uu___104_1321.weak);
            hnf = (uu___104_1321.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1321.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1321.unfold_until);
            unfold_only = (uu___104_1321.unfold_only);
            unfold_fully = (uu___104_1321.unfold_fully);
            unfold_attr = (uu___104_1321.unfold_attr);
            unfold_tac = (uu___104_1321.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1321.pure_subterms_within_computations);
            simplify = (uu___104_1321.simplify);
            erase_universes = (uu___104_1321.erase_universes);
            allow_unbound_universes = (uu___104_1321.allow_unbound_universes);
            reify_ = (uu___104_1321.reify_);
            compress_uvars = (uu___104_1321.compress_uvars);
            no_full_norm = (uu___104_1321.no_full_norm);
            check_no_uvars = (uu___104_1321.check_no_uvars);
            unmeta = (uu___104_1321.unmeta);
            unascribe = (uu___104_1321.unascribe);
            in_full_norm_request = (uu___104_1321.in_full_norm_request)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1322 = fs  in
          {
            beta = (uu___105_1322.beta);
            iota = (uu___105_1322.iota);
            zeta = (uu___105_1322.zeta);
            weak = (uu___105_1322.weak);
            hnf = (uu___105_1322.hnf);
            primops = (uu___105_1322.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1322.unfold_until);
            unfold_only = (uu___105_1322.unfold_only);
            unfold_fully = (uu___105_1322.unfold_fully);
            unfold_attr = (uu___105_1322.unfold_attr);
            unfold_tac = (uu___105_1322.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1322.pure_subterms_within_computations);
            simplify = (uu___105_1322.simplify);
            erase_universes = (uu___105_1322.erase_universes);
            allow_unbound_universes = (uu___105_1322.allow_unbound_universes);
            reify_ = (uu___105_1322.reify_);
            compress_uvars = (uu___105_1322.compress_uvars);
            no_full_norm = (uu___105_1322.no_full_norm);
            check_no_uvars = (uu___105_1322.check_no_uvars);
            unmeta = (uu___105_1322.unmeta);
            unascribe = (uu___105_1322.unascribe);
            in_full_norm_request = (uu___105_1322.in_full_norm_request)
          }
      | UnfoldUntil d ->
          let uu___106_1324 = fs  in
          {
            beta = (uu___106_1324.beta);
            iota = (uu___106_1324.iota);
            zeta = (uu___106_1324.zeta);
            weak = (uu___106_1324.weak);
            hnf = (uu___106_1324.hnf);
            primops = (uu___106_1324.primops);
            do_not_unfold_pure_lets = (uu___106_1324.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1324.unfold_only);
            unfold_fully = (uu___106_1324.unfold_fully);
            unfold_attr = (uu___106_1324.unfold_attr);
            unfold_tac = (uu___106_1324.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1324.pure_subterms_within_computations);
            simplify = (uu___106_1324.simplify);
            erase_universes = (uu___106_1324.erase_universes);
            allow_unbound_universes = (uu___106_1324.allow_unbound_universes);
            reify_ = (uu___106_1324.reify_);
            compress_uvars = (uu___106_1324.compress_uvars);
            no_full_norm = (uu___106_1324.no_full_norm);
            check_no_uvars = (uu___106_1324.check_no_uvars);
            unmeta = (uu___106_1324.unmeta);
            unascribe = (uu___106_1324.unascribe);
            in_full_norm_request = (uu___106_1324.in_full_norm_request)
          }
      | UnfoldOnly lids ->
          let uu___107_1328 = fs  in
          {
            beta = (uu___107_1328.beta);
            iota = (uu___107_1328.iota);
            zeta = (uu___107_1328.zeta);
            weak = (uu___107_1328.weak);
            hnf = (uu___107_1328.hnf);
            primops = (uu___107_1328.primops);
            do_not_unfold_pure_lets = (uu___107_1328.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1328.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1328.unfold_fully);
            unfold_attr = (uu___107_1328.unfold_attr);
            unfold_tac = (uu___107_1328.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1328.pure_subterms_within_computations);
            simplify = (uu___107_1328.simplify);
            erase_universes = (uu___107_1328.erase_universes);
            allow_unbound_universes = (uu___107_1328.allow_unbound_universes);
            reify_ = (uu___107_1328.reify_);
            compress_uvars = (uu___107_1328.compress_uvars);
            no_full_norm = (uu___107_1328.no_full_norm);
            check_no_uvars = (uu___107_1328.check_no_uvars);
            unmeta = (uu___107_1328.unmeta);
            unascribe = (uu___107_1328.unascribe);
            in_full_norm_request = (uu___107_1328.in_full_norm_request)
          }
      | UnfoldFully lids ->
          let uu___108_1334 = fs  in
          {
            beta = (uu___108_1334.beta);
            iota = (uu___108_1334.iota);
            zeta = (uu___108_1334.zeta);
            weak = (uu___108_1334.weak);
            hnf = (uu___108_1334.hnf);
            primops = (uu___108_1334.primops);
            do_not_unfold_pure_lets = (uu___108_1334.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1334.unfold_until);
            unfold_only = (uu___108_1334.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1334.unfold_attr);
            unfold_tac = (uu___108_1334.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1334.pure_subterms_within_computations);
            simplify = (uu___108_1334.simplify);
            erase_universes = (uu___108_1334.erase_universes);
            allow_unbound_universes = (uu___108_1334.allow_unbound_universes);
            reify_ = (uu___108_1334.reify_);
            compress_uvars = (uu___108_1334.compress_uvars);
            no_full_norm = (uu___108_1334.no_full_norm);
            check_no_uvars = (uu___108_1334.check_no_uvars);
            unmeta = (uu___108_1334.unmeta);
            unascribe = (uu___108_1334.unascribe);
            in_full_norm_request = (uu___108_1334.in_full_norm_request)
          }
      | UnfoldAttr attr ->
          let uu___109_1338 = fs  in
          {
            beta = (uu___109_1338.beta);
            iota = (uu___109_1338.iota);
            zeta = (uu___109_1338.zeta);
            weak = (uu___109_1338.weak);
            hnf = (uu___109_1338.hnf);
            primops = (uu___109_1338.primops);
            do_not_unfold_pure_lets = (uu___109_1338.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1338.unfold_until);
            unfold_only = (uu___109_1338.unfold_only);
            unfold_fully = (uu___109_1338.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1338.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1338.pure_subterms_within_computations);
            simplify = (uu___109_1338.simplify);
            erase_universes = (uu___109_1338.erase_universes);
            allow_unbound_universes = (uu___109_1338.allow_unbound_universes);
            reify_ = (uu___109_1338.reify_);
            compress_uvars = (uu___109_1338.compress_uvars);
            no_full_norm = (uu___109_1338.no_full_norm);
            check_no_uvars = (uu___109_1338.check_no_uvars);
            unmeta = (uu___109_1338.unmeta);
            unascribe = (uu___109_1338.unascribe);
            in_full_norm_request = (uu___109_1338.in_full_norm_request)
          }
      | UnfoldTac  ->
          let uu___110_1339 = fs  in
          {
            beta = (uu___110_1339.beta);
            iota = (uu___110_1339.iota);
            zeta = (uu___110_1339.zeta);
            weak = (uu___110_1339.weak);
            hnf = (uu___110_1339.hnf);
            primops = (uu___110_1339.primops);
            do_not_unfold_pure_lets = (uu___110_1339.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1339.unfold_until);
            unfold_only = (uu___110_1339.unfold_only);
            unfold_fully = (uu___110_1339.unfold_fully);
            unfold_attr = (uu___110_1339.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1339.pure_subterms_within_computations);
            simplify = (uu___110_1339.simplify);
            erase_universes = (uu___110_1339.erase_universes);
            allow_unbound_universes = (uu___110_1339.allow_unbound_universes);
            reify_ = (uu___110_1339.reify_);
            compress_uvars = (uu___110_1339.compress_uvars);
            no_full_norm = (uu___110_1339.no_full_norm);
            check_no_uvars = (uu___110_1339.check_no_uvars);
            unmeta = (uu___110_1339.unmeta);
            unascribe = (uu___110_1339.unascribe);
            in_full_norm_request = (uu___110_1339.in_full_norm_request)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1340 = fs  in
          {
            beta = (uu___111_1340.beta);
            iota = (uu___111_1340.iota);
            zeta = (uu___111_1340.zeta);
            weak = (uu___111_1340.weak);
            hnf = (uu___111_1340.hnf);
            primops = (uu___111_1340.primops);
            do_not_unfold_pure_lets = (uu___111_1340.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1340.unfold_until);
            unfold_only = (uu___111_1340.unfold_only);
            unfold_fully = (uu___111_1340.unfold_fully);
            unfold_attr = (uu___111_1340.unfold_attr);
            unfold_tac = (uu___111_1340.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1340.simplify);
            erase_universes = (uu___111_1340.erase_universes);
            allow_unbound_universes = (uu___111_1340.allow_unbound_universes);
            reify_ = (uu___111_1340.reify_);
            compress_uvars = (uu___111_1340.compress_uvars);
            no_full_norm = (uu___111_1340.no_full_norm);
            check_no_uvars = (uu___111_1340.check_no_uvars);
            unmeta = (uu___111_1340.unmeta);
            unascribe = (uu___111_1340.unascribe);
            in_full_norm_request = (uu___111_1340.in_full_norm_request)
          }
      | Simplify  ->
          let uu___112_1341 = fs  in
          {
            beta = (uu___112_1341.beta);
            iota = (uu___112_1341.iota);
            zeta = (uu___112_1341.zeta);
            weak = (uu___112_1341.weak);
            hnf = (uu___112_1341.hnf);
            primops = (uu___112_1341.primops);
            do_not_unfold_pure_lets = (uu___112_1341.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1341.unfold_until);
            unfold_only = (uu___112_1341.unfold_only);
            unfold_fully = (uu___112_1341.unfold_fully);
            unfold_attr = (uu___112_1341.unfold_attr);
            unfold_tac = (uu___112_1341.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1341.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1341.erase_universes);
            allow_unbound_universes = (uu___112_1341.allow_unbound_universes);
            reify_ = (uu___112_1341.reify_);
            compress_uvars = (uu___112_1341.compress_uvars);
            no_full_norm = (uu___112_1341.no_full_norm);
            check_no_uvars = (uu___112_1341.check_no_uvars);
            unmeta = (uu___112_1341.unmeta);
            unascribe = (uu___112_1341.unascribe);
            in_full_norm_request = (uu___112_1341.in_full_norm_request)
          }
      | EraseUniverses  ->
          let uu___113_1342 = fs  in
          {
            beta = (uu___113_1342.beta);
            iota = (uu___113_1342.iota);
            zeta = (uu___113_1342.zeta);
            weak = (uu___113_1342.weak);
            hnf = (uu___113_1342.hnf);
            primops = (uu___113_1342.primops);
            do_not_unfold_pure_lets = (uu___113_1342.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1342.unfold_until);
            unfold_only = (uu___113_1342.unfold_only);
            unfold_fully = (uu___113_1342.unfold_fully);
            unfold_attr = (uu___113_1342.unfold_attr);
            unfold_tac = (uu___113_1342.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1342.pure_subterms_within_computations);
            simplify = (uu___113_1342.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1342.allow_unbound_universes);
            reify_ = (uu___113_1342.reify_);
            compress_uvars = (uu___113_1342.compress_uvars);
            no_full_norm = (uu___113_1342.no_full_norm);
            check_no_uvars = (uu___113_1342.check_no_uvars);
            unmeta = (uu___113_1342.unmeta);
            unascribe = (uu___113_1342.unascribe);
            in_full_norm_request = (uu___113_1342.in_full_norm_request)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1343 = fs  in
          {
            beta = (uu___114_1343.beta);
            iota = (uu___114_1343.iota);
            zeta = (uu___114_1343.zeta);
            weak = (uu___114_1343.weak);
            hnf = (uu___114_1343.hnf);
            primops = (uu___114_1343.primops);
            do_not_unfold_pure_lets = (uu___114_1343.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1343.unfold_until);
            unfold_only = (uu___114_1343.unfold_only);
            unfold_fully = (uu___114_1343.unfold_fully);
            unfold_attr = (uu___114_1343.unfold_attr);
            unfold_tac = (uu___114_1343.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1343.pure_subterms_within_computations);
            simplify = (uu___114_1343.simplify);
            erase_universes = (uu___114_1343.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1343.reify_);
            compress_uvars = (uu___114_1343.compress_uvars);
            no_full_norm = (uu___114_1343.no_full_norm);
            check_no_uvars = (uu___114_1343.check_no_uvars);
            unmeta = (uu___114_1343.unmeta);
            unascribe = (uu___114_1343.unascribe);
            in_full_norm_request = (uu___114_1343.in_full_norm_request)
          }
      | Reify  ->
          let uu___115_1344 = fs  in
          {
            beta = (uu___115_1344.beta);
            iota = (uu___115_1344.iota);
            zeta = (uu___115_1344.zeta);
            weak = (uu___115_1344.weak);
            hnf = (uu___115_1344.hnf);
            primops = (uu___115_1344.primops);
            do_not_unfold_pure_lets = (uu___115_1344.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1344.unfold_until);
            unfold_only = (uu___115_1344.unfold_only);
            unfold_fully = (uu___115_1344.unfold_fully);
            unfold_attr = (uu___115_1344.unfold_attr);
            unfold_tac = (uu___115_1344.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1344.pure_subterms_within_computations);
            simplify = (uu___115_1344.simplify);
            erase_universes = (uu___115_1344.erase_universes);
            allow_unbound_universes = (uu___115_1344.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1344.compress_uvars);
            no_full_norm = (uu___115_1344.no_full_norm);
            check_no_uvars = (uu___115_1344.check_no_uvars);
            unmeta = (uu___115_1344.unmeta);
            unascribe = (uu___115_1344.unascribe);
            in_full_norm_request = (uu___115_1344.in_full_norm_request)
          }
      | CompressUvars  ->
          let uu___116_1345 = fs  in
          {
            beta = (uu___116_1345.beta);
            iota = (uu___116_1345.iota);
            zeta = (uu___116_1345.zeta);
            weak = (uu___116_1345.weak);
            hnf = (uu___116_1345.hnf);
            primops = (uu___116_1345.primops);
            do_not_unfold_pure_lets = (uu___116_1345.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1345.unfold_until);
            unfold_only = (uu___116_1345.unfold_only);
            unfold_fully = (uu___116_1345.unfold_fully);
            unfold_attr = (uu___116_1345.unfold_attr);
            unfold_tac = (uu___116_1345.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1345.pure_subterms_within_computations);
            simplify = (uu___116_1345.simplify);
            erase_universes = (uu___116_1345.erase_universes);
            allow_unbound_universes = (uu___116_1345.allow_unbound_universes);
            reify_ = (uu___116_1345.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1345.no_full_norm);
            check_no_uvars = (uu___116_1345.check_no_uvars);
            unmeta = (uu___116_1345.unmeta);
            unascribe = (uu___116_1345.unascribe);
            in_full_norm_request = (uu___116_1345.in_full_norm_request)
          }
      | NoFullNorm  ->
          let uu___117_1346 = fs  in
          {
            beta = (uu___117_1346.beta);
            iota = (uu___117_1346.iota);
            zeta = (uu___117_1346.zeta);
            weak = (uu___117_1346.weak);
            hnf = (uu___117_1346.hnf);
            primops = (uu___117_1346.primops);
            do_not_unfold_pure_lets = (uu___117_1346.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1346.unfold_until);
            unfold_only = (uu___117_1346.unfold_only);
            unfold_fully = (uu___117_1346.unfold_fully);
            unfold_attr = (uu___117_1346.unfold_attr);
            unfold_tac = (uu___117_1346.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1346.pure_subterms_within_computations);
            simplify = (uu___117_1346.simplify);
            erase_universes = (uu___117_1346.erase_universes);
            allow_unbound_universes = (uu___117_1346.allow_unbound_universes);
            reify_ = (uu___117_1346.reify_);
            compress_uvars = (uu___117_1346.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1346.check_no_uvars);
            unmeta = (uu___117_1346.unmeta);
            unascribe = (uu___117_1346.unascribe);
            in_full_norm_request = (uu___117_1346.in_full_norm_request)
          }
      | CheckNoUvars  ->
          let uu___118_1347 = fs  in
          {
            beta = (uu___118_1347.beta);
            iota = (uu___118_1347.iota);
            zeta = (uu___118_1347.zeta);
            weak = (uu___118_1347.weak);
            hnf = (uu___118_1347.hnf);
            primops = (uu___118_1347.primops);
            do_not_unfold_pure_lets = (uu___118_1347.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1347.unfold_until);
            unfold_only = (uu___118_1347.unfold_only);
            unfold_fully = (uu___118_1347.unfold_fully);
            unfold_attr = (uu___118_1347.unfold_attr);
            unfold_tac = (uu___118_1347.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1347.pure_subterms_within_computations);
            simplify = (uu___118_1347.simplify);
            erase_universes = (uu___118_1347.erase_universes);
            allow_unbound_universes = (uu___118_1347.allow_unbound_universes);
            reify_ = (uu___118_1347.reify_);
            compress_uvars = (uu___118_1347.compress_uvars);
            no_full_norm = (uu___118_1347.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1347.unmeta);
            unascribe = (uu___118_1347.unascribe);
            in_full_norm_request = (uu___118_1347.in_full_norm_request)
          }
      | Unmeta  ->
          let uu___119_1348 = fs  in
          {
            beta = (uu___119_1348.beta);
            iota = (uu___119_1348.iota);
            zeta = (uu___119_1348.zeta);
            weak = (uu___119_1348.weak);
            hnf = (uu___119_1348.hnf);
            primops = (uu___119_1348.primops);
            do_not_unfold_pure_lets = (uu___119_1348.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1348.unfold_until);
            unfold_only = (uu___119_1348.unfold_only);
            unfold_fully = (uu___119_1348.unfold_fully);
            unfold_attr = (uu___119_1348.unfold_attr);
            unfold_tac = (uu___119_1348.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1348.pure_subterms_within_computations);
            simplify = (uu___119_1348.simplify);
            erase_universes = (uu___119_1348.erase_universes);
            allow_unbound_universes = (uu___119_1348.allow_unbound_universes);
            reify_ = (uu___119_1348.reify_);
            compress_uvars = (uu___119_1348.compress_uvars);
            no_full_norm = (uu___119_1348.no_full_norm);
            check_no_uvars = (uu___119_1348.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1348.unascribe);
            in_full_norm_request = (uu___119_1348.in_full_norm_request)
          }
      | Unascribe  ->
          let uu___120_1349 = fs  in
          {
            beta = (uu___120_1349.beta);
            iota = (uu___120_1349.iota);
            zeta = (uu___120_1349.zeta);
            weak = (uu___120_1349.weak);
            hnf = (uu___120_1349.hnf);
            primops = (uu___120_1349.primops);
            do_not_unfold_pure_lets = (uu___120_1349.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1349.unfold_until);
            unfold_only = (uu___120_1349.unfold_only);
            unfold_fully = (uu___120_1349.unfold_fully);
            unfold_attr = (uu___120_1349.unfold_attr);
            unfold_tac = (uu___120_1349.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1349.pure_subterms_within_computations);
            simplify = (uu___120_1349.simplify);
            erase_universes = (uu___120_1349.erase_universes);
            allow_unbound_universes = (uu___120_1349.allow_unbound_universes);
            reify_ = (uu___120_1349.reify_);
            compress_uvars = (uu___120_1349.compress_uvars);
            no_full_norm = (uu___120_1349.no_full_norm);
            check_no_uvars = (uu___120_1349.check_no_uvars);
            unmeta = (uu___120_1349.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1349.in_full_norm_request)
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1388  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1631 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1733 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1744 -> false
  
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
             let uu____2012 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2012 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2024 = FStar_Util.psmap_empty ()  in add_steps uu____2024 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2035 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2035
  
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
    match projectee with | Arg _0 -> true | uu____2181 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2217 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2253 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2324 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2372 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2428 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2470 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2508 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2544 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2560 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2585 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2585 with | (hd1,uu____2599) -> hd1
  
let mk :
  'Auu____2619 .
    'Auu____2619 ->
      FStar_Range.range -> 'Auu____2619 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2673 = FStar_ST.op_Bang r  in
          match uu____2673 with
          | FStar_Pervasives_Native.Some uu____2721 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____2789 =
      FStar_List.map
        (fun uu____2803  ->
           match uu____2803 with
           | (bopt,c) ->
               let uu____2816 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____2818 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____2816 uu____2818) env
       in
    FStar_All.pipe_right uu____2789 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_2821  ->
    match uu___79_2821 with
    | Clos (env,t,uu____2824,uu____2825) ->
        let uu____2870 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____2877 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____2870 uu____2877
    | Univ uu____2878 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2881  ->
    match uu___80_2881 with
    | Arg (c,uu____2883,uu____2884) ->
        let uu____2885 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2885
    | MemoLazy uu____2886 -> "MemoLazy"
    | Abs (uu____2893,bs,uu____2895,uu____2896,uu____2897) ->
        let uu____2902 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2902
    | UnivArgs uu____2907 -> "UnivArgs"
    | Match uu____2914 -> "Match"
    | App (uu____2923,t,uu____2925,uu____2926) ->
        let uu____2927 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2927
    | Meta (uu____2928,m,uu____2930) -> "Meta"
    | Let uu____2931 -> "Let"
    | Cfg uu____2940 -> "Cfg"
    | Debug (t,uu____2942) ->
        let uu____2943 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2943
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2951 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2951 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2982 . 'Auu____2982 Prims.list -> Prims.bool =
  fun uu___81_2988  ->
    match uu___81_2988 with | [] -> true | uu____2991 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3019 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3019
      with
      | uu____3038 ->
          let uu____3039 =
            let uu____3040 = FStar_Syntax_Print.db_to_string x  in
            let uu____3041 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3040
              uu____3041
             in
          failwith uu____3039
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3047 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3047
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3051 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3051
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3055 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3055
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
          let uu____3081 =
            FStar_List.fold_left
              (fun uu____3107  ->
                 fun u1  ->
                   match uu____3107 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3132 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3132 with
                        | (k_u,n1) ->
                            let uu____3147 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3147
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3081 with
          | (uu____3165,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3190 =
                   let uu____3191 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3191  in
                 match uu____3190 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3209 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3217 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3223 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3232 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3241 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3248 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3248 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3265 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3265 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3273 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3281 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3281 with
                                  | (uu____3286,m) -> n1 <= m))
                           in
                        if uu____3273 then rest1 else us1
                    | uu____3291 -> us1)
               | uu____3296 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3300 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3300
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3304 = aux u  in
           match uu____3304 with
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
          log cfg
            (fun uu____3408  ->
               let uu____3409 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3410 = env_to_string env  in
               let uu____3411 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3409 uu____3410 uu____3411);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3420 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3423 ->
                    let uu____3448 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3448
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3449 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3450 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3451 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3452 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3453 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3475 ->
                           let uu____3492 =
                             let uu____3493 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3494 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3493 uu____3494
                              in
                           failwith uu____3492
                       | uu____3497 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3503 =
                        let uu____3504 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3504  in
                      mk uu____3503 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3512 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3512  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3514 = lookup_bvar env x  in
                    (match uu____3514 with
                     | Univ uu____3517 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___125_3521 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___125_3521.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___125_3521.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3527,uu____3528) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3613  ->
                              fun stack1  ->
                                match uu____3613 with
                                | (a,aq) ->
                                    let uu____3625 =
                                      let uu____3626 =
                                        let uu____3633 =
                                          let uu____3634 =
                                            let uu____3665 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____3665, false)  in
                                          Clos uu____3634  in
                                        (uu____3633, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____3626  in
                                    uu____3625 :: stack1) args)
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
                    let uu____3859 = close_binders cfg env bs  in
                    (match uu____3859 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____3906 =
                      let uu____3917 =
                        let uu____3924 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____3924]  in
                      close_binders cfg env uu____3917  in
                    (match uu____3906 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____3947 =
                             let uu____3948 =
                               let uu____3955 =
                                 let uu____3956 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____3956
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____3955, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____3948  in
                           mk uu____3947 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4047 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4047
                      | FStar_Util.Inr c ->
                          let uu____4061 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4061
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4080 =
                        let uu____4081 =
                          let uu____4108 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4108, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4081  in
                      mk uu____4080 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4154 =
                            let uu____4155 =
                              let uu____4162 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4162, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4155  in
                          mk uu____4154 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4214  -> dummy :: env1) env
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
                    let uu____4235 =
                      let uu____4246 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4246
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4265 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___126_4281 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_4281.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_4281.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4265))
                       in
                    (match uu____4235 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___127_4299 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_4299.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_4299.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_4299.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_4299.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4313,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4372  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4397 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4397
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4417  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4441 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4441
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___128_4449 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4449.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4449.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___129_4450 = lb  in
                      let uu____4451 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___129_4450.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___129_4450.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4451;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___129_4450.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___129_4450.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4483  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 head1))

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
          log cfg
            (fun uu____4586  ->
               let uu____4587 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4588 = env_to_string env  in
               let uu____4589 = stack_to_string stack  in
               let uu____4590 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4587 uu____4588 uu____4589 uu____4590);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4595,uu____4596),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____4671 = close_binders cfg env' bs  in
               (match uu____4671 with
                | (bs1,uu____4685) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____4701 =
                      let uu___130_4702 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___130_4702.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___130_4702.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____4701)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____4744 =
                 match uu____4744 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____4815 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____4836 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____4896  ->
                                     fun uu____4897  ->
                                       match (uu____4896, uu____4897) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____4988 = norm_pat env4 p1
                                              in
                                           (match uu____4988 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____4836 with
                            | (pats1,env4) ->
                                ((let uu___131_5070 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___131_5070.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___132_5089 = x  in
                             let uu____5090 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___132_5089.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___132_5089.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5090
                             }  in
                           ((let uu___133_5104 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___133_5104.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___134_5115 = x  in
                             let uu____5116 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5115.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5115.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5116
                             }  in
                           ((let uu___135_5130 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5130.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___136_5146 = x  in
                             let uu____5147 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5146.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5146.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5147
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___137_5156 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5156.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5161 = norm_pat env2 pat  in
                     (match uu____5161 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5206 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5206
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5225 =
                   let uu____5226 =
                     let uu____5249 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5249)  in
                   FStar_Syntax_Syntax.Tm_match uu____5226  in
                 mk uu____5225 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5344 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5433  ->
                                       match uu____5433 with
                                       | (a,q) ->
                                           let uu____5452 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5452, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5344
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5463 =
                       let uu____5470 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5470)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5463
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5482 =
                       let uu____5491 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5491)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5482
                 | uu____5496 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5500 -> failwith "Impossible: unexpected stack element")

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
        let uu____5514 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5563  ->
                  fun uu____5564  ->
                    match (uu____5563, uu____5564) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_5634 = b  in
                          let uu____5635 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_5634.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_5634.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5635
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5514 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5728 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5741 = inline_closure_env cfg env [] t  in
                 let uu____5742 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5741 uu____5742
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5755 = inline_closure_env cfg env [] t  in
                 let uu____5756 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5755 uu____5756
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5802  ->
                           match uu____5802 with
                           | (a,q) ->
                               let uu____5815 =
                                 inline_closure_env cfg env [] a  in
                               (uu____5815, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5830  ->
                           match uu___82_5830 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5834 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5834
                           | f -> f))
                    in
                 let uu____5838 =
                   let uu___139_5839 = c1  in
                   let uu____5840 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5840;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_5839.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5838)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5850  ->
            match uu___83_5850 with
            | FStar_Syntax_Syntax.DECREASES uu____5851 -> false
            | uu____5854 -> true))

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
                   (fun uu___84_5872  ->
                      match uu___84_5872 with
                      | FStar_Syntax_Syntax.DECREASES uu____5873 -> false
                      | uu____5876 -> true))
               in
            let rc1 =
              let uu___140_5878 = rc  in
              let uu____5879 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_5878.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5879;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5888 -> lopt

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
    let uu____5979 =
      let uu____5986 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____5986  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5979  in
  let arg_as_bounded_int uu____6010 =
    match uu____6010 with
    | (a,uu____6022) ->
        let uu____6029 =
          let uu____6030 = FStar_Syntax_Subst.compress a  in
          uu____6030.FStar_Syntax_Syntax.n  in
        (match uu____6029 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6040;
                FStar_Syntax_Syntax.vars = uu____6041;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6043;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6044;_},uu____6045)::[])
             when
             let uu____6084 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6084 "int_to_t" ->
             let uu____6085 =
               let uu____6090 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6090)  in
             FStar_Pervasives_Native.Some uu____6085
         | uu____6095 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6135 = f a  in FStar_Pervasives_Native.Some uu____6135
    | uu____6136 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6184 = f a0 a1  in FStar_Pervasives_Native.Some uu____6184
    | uu____6185 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6227 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____6227)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6276 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____6276)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____6303 =
    match uu____6303 with
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
    unary_op () (fun a406  -> (Obj.magic arg_as_int) a406)
      (fun a407  ->
         fun a408  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6351 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____6351)) a407 a408)
     in
  let binary_int_op f =
    binary_op () (fun a409  -> (Obj.magic arg_as_int) a409)
      (fun a410  ->
         fun a411  ->
           fun a412  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6379 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6379)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6400 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6400)) a414 a415)
     in
  let binary_bool_op f =
    binary_op () (fun a416  -> (Obj.magic arg_as_bool) a416)
      (fun a417  ->
         fun a418  ->
           fun a419  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6428 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6428)) a417
               a418 a419)
     in
  let binary_string_op f =
    binary_op () (fun a420  -> (Obj.magic arg_as_string) a420)
      (fun a421  ->
         fun a422  ->
           fun a423  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6456 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6456)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6564 =
          let uu____6573 = as_a a  in
          let uu____6576 = as_b b  in (uu____6573, uu____6576)  in
        (match uu____6564 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6591 =
               let uu____6592 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6592  in
             FStar_Pervasives_Native.Some uu____6591
         | uu____6593 -> FStar_Pervasives_Native.None)
    | uu____6602 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6616 =
        let uu____6617 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6617  in
      mk uu____6616 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6627 =
      let uu____6630 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6630  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6627  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6662 =
      let uu____6663 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6663  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6662
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6681 = arg_as_string a1  in
        (match uu____6681 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6687 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6687 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6700 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6700
              | uu____6701 -> FStar_Pervasives_Native.None)
         | uu____6706 -> FStar_Pervasives_Native.None)
    | uu____6709 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6719 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6719
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6748 =
          let uu____6769 = arg_as_string fn  in
          let uu____6772 = arg_as_int from_line  in
          let uu____6775 = arg_as_int from_col  in
          let uu____6778 = arg_as_int to_line  in
          let uu____6781 = arg_as_int to_col  in
          (uu____6769, uu____6772, uu____6775, uu____6778, uu____6781)  in
        (match uu____6748 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6812 =
                 let uu____6813 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6814 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6813 uu____6814  in
               let uu____6815 =
                 let uu____6816 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6817 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6816 uu____6817  in
               FStar_Range.mk_range fn1 uu____6812 uu____6815  in
             let uu____6818 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6818
         | uu____6819 -> FStar_Pervasives_Native.None)
    | uu____6840 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6867)::(a1,uu____6869)::(a2,uu____6871)::[] ->
        let uu____6908 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6908 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6921 -> FStar_Pervasives_Native.None)
    | uu____6922 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6949)::[] ->
        let uu____6958 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____6958 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6964 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6964
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6965 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6989 =
      let uu____7004 =
        let uu____7019 =
          let uu____7034 =
            let uu____7049 =
              let uu____7064 =
                let uu____7079 =
                  let uu____7094 =
                    let uu____7109 =
                      let uu____7124 =
                        let uu____7139 =
                          let uu____7154 =
                            let uu____7169 =
                              let uu____7184 =
                                let uu____7199 =
                                  let uu____7214 =
                                    let uu____7229 =
                                      let uu____7244 =
                                        let uu____7259 =
                                          let uu____7274 =
                                            let uu____7289 =
                                              let uu____7304 =
                                                let uu____7317 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7317,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a424  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a424)
                                                     (fun a425  ->
                                                        fun a426  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a425 a426)))
                                                 in
                                              let uu____7324 =
                                                let uu____7339 =
                                                  let uu____7352 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7352,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a427  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a427)
                                                       (fun a428  ->
                                                          fun a429  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a428 a429)))
                                                   in
                                                let uu____7359 =
                                                  let uu____7374 =
                                                    let uu____7389 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7389,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7398 =
                                                    let uu____7415 =
                                                      let uu____7430 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7430,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7415]  in
                                                  uu____7374 :: uu____7398
                                                   in
                                                uu____7339 :: uu____7359  in
                                              uu____7304 :: uu____7324  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7289
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7274
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a430  ->
                                                (Obj.magic arg_as_string)
                                                  a430)
                                             (fun a431  ->
                                                fun a432  ->
                                                  fun a433  ->
                                                    (Obj.magic
                                                       string_compare') a431
                                                      a432 a433)))
                                          :: uu____7259
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a434  ->
                                              (Obj.magic arg_as_bool) a434)
                                           (fun a435  ->
                                              fun a436  ->
                                                (Obj.magic string_of_bool1)
                                                  a435 a436)))
                                        :: uu____7244
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a437  ->
                                            (Obj.magic arg_as_int) a437)
                                         (fun a438  ->
                                            fun a439  ->
                                              (Obj.magic string_of_int1) a438
                                                a439)))
                                      :: uu____7229
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a440  ->
                                          (Obj.magic arg_as_int) a440)
                                       (fun a441  ->
                                          (Obj.magic arg_as_char) a441)
                                       (fun a442  ->
                                          fun a443  ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a442 a443)
                                       (fun a444  ->
                                          fun a445  ->
                                            fun a446  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____7621 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7621 y)) a444
                                                a445 a446)))
                                    :: uu____7214
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7199
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7184
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7169
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7154
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7139
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7124
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a447  -> (Obj.magic arg_as_int) a447)
                         (fun a448  ->
                            fun a449  ->
                              fun a450  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7788 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7788)) a448 a449 a450)))
                      :: uu____7109
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a451  -> (Obj.magic arg_as_int) a451)
                       (fun a452  ->
                          fun a453  ->
                            fun a454  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7814 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7814)) a452 a453 a454)))
                    :: uu____7094
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a455  -> (Obj.magic arg_as_int) a455)
                     (fun a456  ->
                        fun a457  ->
                          fun a458  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7840 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7840)) a456 a457 a458)))
                  :: uu____7079
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a459  -> (Obj.magic arg_as_int) a459)
                   (fun a460  ->
                      fun a461  ->
                        fun a462  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7866 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7866)) a460 a461 a462)))
                :: uu____7064
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7049
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7034
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7019
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7004
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6989
     in
  let weak_ops =
    let uu____8005 =
      let uu____8024 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8024, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8005]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8108 =
        let uu____8109 =
          let uu____8110 = FStar_Syntax_Syntax.as_arg c  in [uu____8110]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8109  in
      uu____8108 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8160 =
                let uu____8173 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____8173, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8189  ->
                                    fun uu____8190  ->
                                      match (uu____8189, uu____8190) with
                                      | ((int_to_t1,x),(uu____8209,y)) ->
                                          let uu____8219 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8219)) a464 a465 a466)))
                 in
              let uu____8220 =
                let uu____8235 =
                  let uu____8248 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____8248, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8264  ->
                                      fun uu____8265  ->
                                        match (uu____8264, uu____8265) with
                                        | ((int_to_t1,x),(uu____8284,y)) ->
                                            let uu____8294 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8294)) a468 a469 a470)))
                   in
                let uu____8295 =
                  let uu____8310 =
                    let uu____8323 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____8323, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8339  ->
                                        fun uu____8340  ->
                                          match (uu____8339, uu____8340) with
                                          | ((int_to_t1,x),(uu____8359,y)) ->
                                              let uu____8369 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8369)) a472 a473 a474)))
                     in
                  let uu____8370 =
                    let uu____8385 =
                      let uu____8398 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8398, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8410  ->
                                        match uu____8410 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____8385]  in
                  uu____8310 :: uu____8370  in
                uu____8235 :: uu____8295  in
              uu____8160 :: uu____8220))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8524 =
                let uu____8537 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8537, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8553  ->
                                    fun uu____8554  ->
                                      match (uu____8553, uu____8554) with
                                      | ((int_to_t1,x),(uu____8573,y)) ->
                                          let uu____8583 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8583)) a479 a480 a481)))
                 in
              let uu____8584 =
                let uu____8599 =
                  let uu____8612 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8612, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8628  ->
                                      fun uu____8629  ->
                                        match (uu____8628, uu____8629) with
                                        | ((int_to_t1,x),(uu____8648,y)) ->
                                            let uu____8658 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8658)) a483 a484 a485)))
                   in
                [uu____8599]  in
              uu____8524 :: uu____8584))
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
    | (_typ,uu____8770)::(a1,uu____8772)::(a2,uu____8774)::[] ->
        let uu____8811 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8811 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8817 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8817.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8817.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_8821 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_8821.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_8821.FStar_Syntax_Syntax.vars)
                })
         | uu____8822 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8824)::uu____8825::(a1,uu____8827)::(a2,uu____8829)::[] ->
        let uu____8878 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8878 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8884 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8884.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8884.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_8888 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_8888.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_8888.FStar_Syntax_Syntax.vars)
                })
         | uu____8889 -> FStar_Pervasives_Native.None)
    | uu____8890 -> failwith "Unexpected number of arguments"  in
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
    let uu____8942 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8942 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8987 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8987) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9047  ->
           fun subst1  ->
             match uu____9047 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9088,uu____9089)) ->
                      let uu____9148 = b  in
                      (match uu____9148 with
                       | (bv,uu____9156) ->
                           let uu____9157 =
                             let uu____9158 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____9158  in
                           if uu____9157
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____9163 = unembed_binder term1  in
                              match uu____9163 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____9170 =
                                      let uu___143_9171 = bv  in
                                      let uu____9172 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_9171.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_9171.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____9172
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____9170
                                     in
                                  let b_for_x =
                                    let uu____9176 =
                                      let uu____9183 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____9183)
                                       in
                                    FStar_Syntax_Syntax.NT uu____9176  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_9193  ->
                                         match uu___85_9193 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____9194,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9196;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9197;_})
                                             ->
                                             let uu____9202 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____9202
                                         | uu____9203 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____9204 -> subst1)) env []
  
let reduce_primops :
  'Auu____9221 'Auu____9222 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9221) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9222 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____9264 = FStar_Syntax_Util.head_and_args tm  in
             match uu____9264 with
             | (head1,args) ->
                 let uu____9301 =
                   let uu____9302 = FStar_Syntax_Util.un_uinst head1  in
                   uu____9302.FStar_Syntax_Syntax.n  in
                 (match uu____9301 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____9306 = find_prim_step cfg fv  in
                      (match uu____9306 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____9328  ->
                                   let uu____9329 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____9330 =
                                     FStar_Util.string_of_int l  in
                                   let uu____9337 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____9329 uu____9330 uu____9337);
                              tm)
                           else
                             (let uu____9339 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____9339 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9450  ->
                                        let uu____9451 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9451);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9454  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9456 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9456 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9462  ->
                                              let uu____9463 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9463);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9469  ->
                                              let uu____9470 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9471 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9470 uu____9471);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9472 ->
                           (log_primops cfg
                              (fun uu____9476  ->
                                 let uu____9477 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9477);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9481  ->
                            let uu____9482 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9482);
                       (match args with
                        | (a1,uu____9484)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9501 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9513  ->
                            let uu____9514 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9514);
                       (match args with
                        | (t,uu____9516)::(r,uu____9518)::[] ->
                            let uu____9545 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____9545 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___144_9549 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___144_9549.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___144_9549.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9552 -> tm))
                  | uu____9561 -> tm))
  
let reduce_equality :
  'Auu____9566 'Auu____9567 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9566) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9567 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_9605 = cfg  in
         {
           steps =
             (let uu___146_9608 = default_steps  in
              {
                beta = (uu___146_9608.beta);
                iota = (uu___146_9608.iota);
                zeta = (uu___146_9608.zeta);
                weak = (uu___146_9608.weak);
                hnf = (uu___146_9608.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_9608.do_not_unfold_pure_lets);
                unfold_until = (uu___146_9608.unfold_until);
                unfold_only = (uu___146_9608.unfold_only);
                unfold_fully = (uu___146_9608.unfold_fully);
                unfold_attr = (uu___146_9608.unfold_attr);
                unfold_tac = (uu___146_9608.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_9608.pure_subterms_within_computations);
                simplify = (uu___146_9608.simplify);
                erase_universes = (uu___146_9608.erase_universes);
                allow_unbound_universes =
                  (uu___146_9608.allow_unbound_universes);
                reify_ = (uu___146_9608.reify_);
                compress_uvars = (uu___146_9608.compress_uvars);
                no_full_norm = (uu___146_9608.no_full_norm);
                check_no_uvars = (uu___146_9608.check_no_uvars);
                unmeta = (uu___146_9608.unmeta);
                unascribe = (uu___146_9608.unascribe);
                in_full_norm_request = (uu___146_9608.in_full_norm_request)
              });
           tcenv = (uu___145_9605.tcenv);
           debug = (uu___145_9605.debug);
           delta_level = (uu___145_9605.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_9605.strong);
           memoize_lazy = (uu___145_9605.memoize_lazy);
           normalize_pure_lets = (uu___145_9605.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9612 .
    FStar_Syntax_Syntax.term -> 'Auu____9612 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9625 =
        let uu____9632 =
          let uu____9633 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9633.FStar_Syntax_Syntax.n  in
        (uu____9632, args)  in
      match uu____9625 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9639::uu____9640::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9644::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9649::uu____9650::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9653 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9664  ->
    match uu___86_9664 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9670 =
          let uu____9673 =
            let uu____9674 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9674  in
          [uu____9673]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9670
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9680 =
          let uu____9683 =
            let uu____9684 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9684  in
          [uu____9683]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9680
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9700 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9700) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9742 =
          let uu____9747 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9747 s  in
        match uu____9742 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9763 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9763
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9780::(tm,uu____9782)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9811)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9832)::uu____9833::(tm,uu____9835)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9872 =
            let uu____9877 = full_norm steps  in parse_steps uu____9877  in
          (match uu____9872 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9916 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9933  ->
    match uu___87_9933 with
    | (App
        (uu____9936,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9937;
                      FStar_Syntax_Syntax.vars = uu____9938;_},uu____9939,uu____9940))::uu____9941
        -> true
    | uu____9948 -> false
  
let firstn :
  'Auu____9954 .
    Prims.int ->
      'Auu____9954 Prims.list ->
        ('Auu____9954 Prims.list,'Auu____9954 Prims.list)
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
          (uu____9990,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9991;
                        FStar_Syntax_Syntax.vars = uu____9992;_},uu____9993,uu____9994))::uu____9995
          -> (cfg.steps).reify_
      | uu____10002 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10186 ->
                   let uu____10211 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10211
               | uu____10212 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____10220  ->
               let uu____10221 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10222 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10223 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10230 =
                 let uu____10231 =
                   let uu____10234 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10234
                    in
                 stack_to_string uu____10231  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10221 uu____10222 uu____10223 uu____10230);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10257 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10258 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____10259 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10260;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10261;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10264;
                 FStar_Syntax_Syntax.fv_delta = uu____10265;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10266;
                 FStar_Syntax_Syntax.fv_delta = uu____10267;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10268);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____10275 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10311 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10311)
               ->
               let cfg' =
                 let uu___147_10313 = cfg  in
                 {
                   steps =
                     (let uu___148_10316 = cfg.steps  in
                      {
                        beta = (uu___148_10316.beta);
                        iota = (uu___148_10316.iota);
                        zeta = (uu___148_10316.zeta);
                        weak = (uu___148_10316.weak);
                        hnf = (uu___148_10316.hnf);
                        primops = (uu___148_10316.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_10316.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_10316.unfold_attr);
                        unfold_tac = (uu___148_10316.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_10316.pure_subterms_within_computations);
                        simplify = (uu___148_10316.simplify);
                        erase_universes = (uu___148_10316.erase_universes);
                        allow_unbound_universes =
                          (uu___148_10316.allow_unbound_universes);
                        reify_ = (uu___148_10316.reify_);
                        compress_uvars = (uu___148_10316.compress_uvars);
                        no_full_norm = (uu___148_10316.no_full_norm);
                        check_no_uvars = (uu___148_10316.check_no_uvars);
                        unmeta = (uu___148_10316.unmeta);
                        unascribe = (uu___148_10316.unascribe);
                        in_full_norm_request =
                          (uu___148_10316.in_full_norm_request)
                      });
                   tcenv = (uu___147_10313.tcenv);
                   debug = (uu___147_10313.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_10313.primitive_steps);
                   strong = (uu___147_10313.strong);
                   memoize_lazy = (uu___147_10313.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10321 = get_norm_request (norm cfg' env []) args  in
               (match uu____10321 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10352  ->
                              fun stack1  ->
                                match uu____10352 with
                                | (a,aq) ->
                                    let uu____10364 =
                                      let uu____10365 =
                                        let uu____10372 =
                                          let uu____10373 =
                                            let uu____10404 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10404, false)  in
                                          Clos uu____10373  in
                                        (uu____10372, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10365  in
                                    uu____10364 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10488  ->
                          let uu____10489 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10489);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10511 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10516  ->
                                match uu___88_10516 with
                                | UnfoldUntil uu____10517 -> true
                                | UnfoldOnly uu____10518 -> true
                                | UnfoldFully uu____10521 -> true
                                | uu____10524 -> false))
                         in
                      if uu____10511
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_10529 = cfg  in
                      let uu____10530 =
                        let uu___150_10531 = to_fsteps s  in
                        {
                          beta = (uu___150_10531.beta);
                          iota = (uu___150_10531.iota);
                          zeta = (uu___150_10531.zeta);
                          weak = (uu___150_10531.weak);
                          hnf = (uu___150_10531.hnf);
                          primops = (uu___150_10531.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_10531.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_10531.unfold_until);
                          unfold_only = (uu___150_10531.unfold_only);
                          unfold_fully = (uu___150_10531.unfold_fully);
                          unfold_attr = (uu___150_10531.unfold_attr);
                          unfold_tac = (uu___150_10531.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_10531.pure_subterms_within_computations);
                          simplify = (uu___150_10531.simplify);
                          erase_universes = (uu___150_10531.erase_universes);
                          allow_unbound_universes =
                            (uu___150_10531.allow_unbound_universes);
                          reify_ = (uu___150_10531.reify_);
                          compress_uvars = (uu___150_10531.compress_uvars);
                          no_full_norm = (uu___150_10531.no_full_norm);
                          check_no_uvars = (uu___150_10531.check_no_uvars);
                          unmeta = (uu___150_10531.unmeta);
                          unascribe = (uu___150_10531.unascribe);
                          in_full_norm_request = true
                        }  in
                      {
                        steps = uu____10530;
                        tcenv = (uu___149_10529.tcenv);
                        debug = (uu___149_10529.debug);
                        delta_level;
                        primitive_steps = (uu___149_10529.primitive_steps);
                        strong = (uu___149_10529.strong);
                        memoize_lazy = (uu___149_10529.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10540 =
                          let uu____10541 =
                            let uu____10546 = FStar_Util.now ()  in
                            (t1, uu____10546)  in
                          Debug uu____10541  in
                        uu____10540 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10550 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10550
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10559 =
                      let uu____10566 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10566, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10559  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10576 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10576  in
               let uu____10577 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10577
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10583  ->
                       let uu____10584 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10585 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10584 uu____10585);
                  if b
                  then
                    (let uu____10586 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10586 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10594 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10594) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10600  ->
                               match uu___89_10600 with
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
                          (let uu____10610 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10610))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10629) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10664,uu____10665) -> false)))
                     in
                  let uu____10682 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____10698 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____10698 then (true, true) else (false, false)
                     in
                  match uu____10682 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____10711  ->
                            let uu____10712 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____10713 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____10714 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____10712 uu____10713 uu____10714);
                       if should_delta2
                       then
                         (let uu____10715 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_10731 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_10734 = cfg.steps  in
                                      {
                                        beta = (uu___152_10734.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_10734.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_10734.unfold_attr);
                                        unfold_tac =
                                          (uu___152_10734.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_10734.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_10734.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_10734.allow_unbound_universes);
                                        reify_ = (uu___152_10734.reify_);
                                        compress_uvars =
                                          (uu___152_10734.compress_uvars);
                                        no_full_norm =
                                          (uu___152_10734.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_10734.check_no_uvars);
                                        unmeta = (uu___152_10734.unmeta);
                                        unascribe =
                                          (uu___152_10734.unascribe);
                                        in_full_norm_request =
                                          (uu___152_10734.in_full_norm_request)
                                      });
                                   tcenv = (uu___151_10731.tcenv);
                                   debug = (uu___151_10731.debug);
                                   delta_level = (uu___151_10731.delta_level);
                                   primitive_steps =
                                     (uu___151_10731.primitive_steps);
                                   strong = (uu___151_10731.strong);
                                   memoize_lazy =
                                     (uu___151_10731.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_10731.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____10715 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10748 = lookup_bvar env x  in
               (match uu____10748 with
                | Univ uu____10749 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10798 = FStar_ST.op_Bang r  in
                      (match uu____10798 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10916  ->
                                 let uu____10917 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10918 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10917
                                   uu____10918);
                            (let uu____10919 =
                               let uu____10920 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10920.FStar_Syntax_Syntax.n  in
                             match uu____10919 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10923 ->
                                 norm cfg env2 stack t'
                             | uu____10940 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11010)::uu____11011 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11020)::uu____11021 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11033,uu____11034))::stack_rest ->
                    (match c with
                     | Univ uu____11038 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11047 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11068  ->
                                    let uu____11069 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11069);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11109  ->
                                    let uu____11110 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11110);
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
                       (fun uu____11188  ->
                          let uu____11189 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11189);
                     norm cfg env stack1 t1)
                | (Debug uu____11190)::uu____11191 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11201 = cfg.steps  in
                             {
                               beta = (uu___153_11201.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11201.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11201.unfold_until);
                               unfold_only = (uu___153_11201.unfold_only);
                               unfold_fully = (uu___153_11201.unfold_fully);
                               unfold_attr = (uu___153_11201.unfold_attr);
                               unfold_tac = (uu___153_11201.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11201.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11201.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11201.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11201.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11201.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11203 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11203.tcenv);
                               debug = (uu___154_11203.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11203.primitive_steps);
                               strong = (uu___154_11203.strong);
                               memoize_lazy = (uu___154_11203.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11203.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11205 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11205 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11247  -> dummy :: env1) env)
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
                                          let uu____11284 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11284)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11289 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11289.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11289.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11290 -> lopt  in
                           (log cfg
                              (fun uu____11296  ->
                                 let uu____11297 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11297);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11306 = cfg  in
                               {
                                 steps = (uu___156_11306.steps);
                                 tcenv = (uu___156_11306.tcenv);
                                 debug = (uu___156_11306.debug);
                                 delta_level = (uu___156_11306.delta_level);
                                 primitive_steps =
                                   (uu___156_11306.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11306.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11306.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11317)::uu____11318 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11330 = cfg.steps  in
                             {
                               beta = (uu___153_11330.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11330.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11330.unfold_until);
                               unfold_only = (uu___153_11330.unfold_only);
                               unfold_fully = (uu___153_11330.unfold_fully);
                               unfold_attr = (uu___153_11330.unfold_attr);
                               unfold_tac = (uu___153_11330.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11330.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11330.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11330.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11330.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11330.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11332 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11332.tcenv);
                               debug = (uu___154_11332.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11332.primitive_steps);
                               strong = (uu___154_11332.strong);
                               memoize_lazy = (uu___154_11332.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11332.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11334 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11334 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11376  -> dummy :: env1) env)
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
                                          let uu____11413 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11413)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11418 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11418.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11418.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11419 -> lopt  in
                           (log cfg
                              (fun uu____11425  ->
                                 let uu____11426 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11426);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11435 = cfg  in
                               {
                                 steps = (uu___156_11435.steps);
                                 tcenv = (uu___156_11435.tcenv);
                                 debug = (uu___156_11435.debug);
                                 delta_level = (uu___156_11435.delta_level);
                                 primitive_steps =
                                   (uu___156_11435.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11435.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11435.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11446)::uu____11447 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11461 = cfg.steps  in
                             {
                               beta = (uu___153_11461.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11461.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11461.unfold_until);
                               unfold_only = (uu___153_11461.unfold_only);
                               unfold_fully = (uu___153_11461.unfold_fully);
                               unfold_attr = (uu___153_11461.unfold_attr);
                               unfold_tac = (uu___153_11461.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11461.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11461.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11461.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11461.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11461.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11463 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11463.tcenv);
                               debug = (uu___154_11463.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11463.primitive_steps);
                               strong = (uu___154_11463.strong);
                               memoize_lazy = (uu___154_11463.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11463.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11465 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11465 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11507  -> dummy :: env1) env)
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
                                          let uu____11544 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11544)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11549 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11549.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11549.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11550 -> lopt  in
                           (log cfg
                              (fun uu____11556  ->
                                 let uu____11557 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11557);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11566 = cfg  in
                               {
                                 steps = (uu___156_11566.steps);
                                 tcenv = (uu___156_11566.tcenv);
                                 debug = (uu___156_11566.debug);
                                 delta_level = (uu___156_11566.delta_level);
                                 primitive_steps =
                                   (uu___156_11566.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11566.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11566.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11577)::uu____11578 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11592 = cfg.steps  in
                             {
                               beta = (uu___153_11592.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11592.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11592.unfold_until);
                               unfold_only = (uu___153_11592.unfold_only);
                               unfold_fully = (uu___153_11592.unfold_fully);
                               unfold_attr = (uu___153_11592.unfold_attr);
                               unfold_tac = (uu___153_11592.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11592.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11592.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11592.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11592.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11592.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11594 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11594.tcenv);
                               debug = (uu___154_11594.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11594.primitive_steps);
                               strong = (uu___154_11594.strong);
                               memoize_lazy = (uu___154_11594.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11594.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11596 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11596 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11638  -> dummy :: env1) env)
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
                                          let uu____11675 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11675)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11680 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11680.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11680.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11681 -> lopt  in
                           (log cfg
                              (fun uu____11687  ->
                                 let uu____11688 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11688);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11697 = cfg  in
                               {
                                 steps = (uu___156_11697.steps);
                                 tcenv = (uu___156_11697.tcenv);
                                 debug = (uu___156_11697.debug);
                                 delta_level = (uu___156_11697.delta_level);
                                 primitive_steps =
                                   (uu___156_11697.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11697.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11697.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11708)::uu____11709 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11727 = cfg.steps  in
                             {
                               beta = (uu___153_11727.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11727.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11727.unfold_until);
                               unfold_only = (uu___153_11727.unfold_only);
                               unfold_fully = (uu___153_11727.unfold_fully);
                               unfold_attr = (uu___153_11727.unfold_attr);
                               unfold_tac = (uu___153_11727.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11727.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11727.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11727.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11727.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11727.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11729 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11729.tcenv);
                               debug = (uu___154_11729.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11729.primitive_steps);
                               strong = (uu___154_11729.strong);
                               memoize_lazy = (uu___154_11729.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11729.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11731 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11731 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11773  -> dummy :: env1) env)
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
                                          let uu____11810 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11810)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11815 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11815.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11815.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11816 -> lopt  in
                           (log cfg
                              (fun uu____11822  ->
                                 let uu____11823 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11823);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11832 = cfg  in
                               {
                                 steps = (uu___156_11832.steps);
                                 tcenv = (uu___156_11832.tcenv);
                                 debug = (uu___156_11832.debug);
                                 delta_level = (uu___156_11832.delta_level);
                                 primitive_steps =
                                   (uu___156_11832.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11832.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11832.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11846 = cfg.steps  in
                             {
                               beta = (uu___153_11846.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11846.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11846.unfold_until);
                               unfold_only = (uu___153_11846.unfold_only);
                               unfold_fully = (uu___153_11846.unfold_fully);
                               unfold_attr = (uu___153_11846.unfold_attr);
                               unfold_tac = (uu___153_11846.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11846.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11846.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11846.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11846.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11846.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11848 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11848.tcenv);
                               debug = (uu___154_11848.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11848.primitive_steps);
                               strong = (uu___154_11848.strong);
                               memoize_lazy = (uu___154_11848.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11848.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11850 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11850 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11892  -> dummy :: env1) env)
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
                                          let uu____11929 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11929)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11934 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11934.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11934.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11935 -> lopt  in
                           (log cfg
                              (fun uu____11941  ->
                                 let uu____11942 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11942);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11951 = cfg  in
                               {
                                 steps = (uu___156_11951.steps);
                                 tcenv = (uu___156_11951.tcenv);
                                 debug = (uu___156_11951.debug);
                                 delta_level = (uu___156_11951.delta_level);
                                 primitive_steps =
                                   (uu___156_11951.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11951.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11951.normalize_pure_lets)
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
                      (fun uu____12000  ->
                         fun stack1  ->
                           match uu____12000 with
                           | (a,aq) ->
                               let uu____12012 =
                                 let uu____12013 =
                                   let uu____12020 =
                                     let uu____12021 =
                                       let uu____12052 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12052, false)  in
                                     Clos uu____12021  in
                                   (uu____12020, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12013  in
                               uu____12012 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12136  ->
                     let uu____12137 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12137);
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
                             ((let uu___157_12173 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12173.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12173.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12174 ->
                      let uu____12179 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12179)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12182 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12182 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12213 =
                          let uu____12214 =
                            let uu____12221 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_12223 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_12223.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_12223.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12221)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12214  in
                        mk uu____12213 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12242 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12242
               else
                 (let uu____12244 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12244 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12252 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12276  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12252 c1  in
                      let t2 =
                        let uu____12298 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12298 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12409)::uu____12410 ->
                    (log cfg
                       (fun uu____12423  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12424)::uu____12425 ->
                    (log cfg
                       (fun uu____12436  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12437,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12438;
                                   FStar_Syntax_Syntax.vars = uu____12439;_},uu____12440,uu____12441))::uu____12442
                    ->
                    (log cfg
                       (fun uu____12451  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12452)::uu____12453 ->
                    (log cfg
                       (fun uu____12464  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12465 ->
                    (log cfg
                       (fun uu____12468  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____12472  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12489 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12489
                         | FStar_Util.Inr c ->
                             let uu____12497 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12497
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12510 =
                               let uu____12511 =
                                 let uu____12538 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12538, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12511
                                in
                             mk uu____12510 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12557 ->
                           let uu____12558 =
                             let uu____12559 =
                               let uu____12560 =
                                 let uu____12587 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12587, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12560
                                in
                             mk uu____12559 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12558))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if (cfg.steps).iota
                 then
                   let uu___159_12664 = cfg  in
                   {
                     steps =
                       (let uu___160_12667 = cfg.steps  in
                        {
                          beta = (uu___160_12667.beta);
                          iota = (uu___160_12667.iota);
                          zeta = (uu___160_12667.zeta);
                          weak = true;
                          hnf = (uu___160_12667.hnf);
                          primops = (uu___160_12667.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_12667.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_12667.unfold_until);
                          unfold_only = (uu___160_12667.unfold_only);
                          unfold_fully = (uu___160_12667.unfold_fully);
                          unfold_attr = (uu___160_12667.unfold_attr);
                          unfold_tac = (uu___160_12667.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_12667.pure_subterms_within_computations);
                          simplify = (uu___160_12667.simplify);
                          erase_universes = (uu___160_12667.erase_universes);
                          allow_unbound_universes =
                            (uu___160_12667.allow_unbound_universes);
                          reify_ = (uu___160_12667.reify_);
                          compress_uvars = (uu___160_12667.compress_uvars);
                          no_full_norm = (uu___160_12667.no_full_norm);
                          check_no_uvars = (uu___160_12667.check_no_uvars);
                          unmeta = (uu___160_12667.unmeta);
                          unascribe = (uu___160_12667.unascribe);
                          in_full_norm_request =
                            (uu___160_12667.in_full_norm_request)
                        });
                     tcenv = (uu___159_12664.tcenv);
                     debug = (uu___159_12664.debug);
                     delta_level = (uu___159_12664.delta_level);
                     primitive_steps = (uu___159_12664.primitive_steps);
                     strong = (uu___159_12664.strong);
                     memoize_lazy = (uu___159_12664.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_12664.normalize_pure_lets)
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
                         let uu____12703 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12703 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_12723 = cfg  in
                               let uu____12724 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_12723.steps);
                                 tcenv = uu____12724;
                                 debug = (uu___161_12723.debug);
                                 delta_level = (uu___161_12723.delta_level);
                                 primitive_steps =
                                   (uu___161_12723.primitive_steps);
                                 strong = (uu___161_12723.strong);
                                 memoize_lazy = (uu___161_12723.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_12723.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12729 =
                                 let uu____12730 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12730  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12729
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_12733 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_12733.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_12733.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_12733.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_12733.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12734 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12734
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12745,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12746;
                               FStar_Syntax_Syntax.lbunivs = uu____12747;
                               FStar_Syntax_Syntax.lbtyp = uu____12748;
                               FStar_Syntax_Syntax.lbeff = uu____12749;
                               FStar_Syntax_Syntax.lbdef = uu____12750;
                               FStar_Syntax_Syntax.lbattrs = uu____12751;
                               FStar_Syntax_Syntax.lbpos = uu____12752;_}::uu____12753),uu____12754)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12794 =
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
               if uu____12794
               then
                 let binder =
                   let uu____12796 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12796  in
                 let env1 =
                   let uu____12806 =
                     let uu____12813 =
                       let uu____12814 =
                         let uu____12845 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12845,
                           false)
                          in
                       Clos uu____12814  in
                     ((FStar_Pervasives_Native.Some binder), uu____12813)  in
                   uu____12806 :: env  in
                 (log cfg
                    (fun uu____12938  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12942  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12943 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12943))
                 else
                   (let uu____12945 =
                      let uu____12950 =
                        let uu____12951 =
                          let uu____12952 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12952
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12951]  in
                      FStar_Syntax_Subst.open_term uu____12950 body  in
                    match uu____12945 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12961  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12969 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12969  in
                            FStar_Util.Inl
                              (let uu___163_12979 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_12979.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_12979.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12982  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_12984 = lb  in
                             let uu____12985 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_12984.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_12984.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12985;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_12984.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_12984.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13020  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_13043 = cfg  in
                             {
                               steps = (uu___165_13043.steps);
                               tcenv = (uu___165_13043.tcenv);
                               debug = (uu___165_13043.debug);
                               delta_level = (uu___165_13043.delta_level);
                               primitive_steps =
                                 (uu___165_13043.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_13043.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_13043.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13046  ->
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
               let uu____13063 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13063 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13099 =
                               let uu___166_13100 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_13100.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_13100.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13099  in
                           let uu____13101 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13101 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13127 =
                                   FStar_List.map (fun uu____13143  -> dummy)
                                     lbs1
                                    in
                                 let uu____13144 =
                                   let uu____13153 =
                                     FStar_List.map
                                       (fun uu____13173  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13153 env  in
                                 FStar_List.append uu____13127 uu____13144
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13197 =
                                       let uu___167_13198 = rc  in
                                       let uu____13199 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_13198.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13199;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_13198.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13197
                                 | uu____13206 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_13210 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_13210.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_13210.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_13210.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_13210.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13220 =
                        FStar_List.map (fun uu____13236  -> dummy) lbs2  in
                      FStar_List.append uu____13220 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13244 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13244 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_13260 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_13260.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_13260.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13287 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13287
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13306 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13382  ->
                        match uu____13382 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_13503 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_13503.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_13503.FStar_Syntax_Syntax.sort)
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
               (match uu____13306 with
                | (rec_env,memos,uu____13716) ->
                    let uu____13769 =
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
                             let uu____14080 =
                               let uu____14087 =
                                 let uu____14088 =
                                   let uu____14119 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14119, false)
                                    in
                                 Clos uu____14088  in
                               (FStar_Pervasives_Native.None, uu____14087)
                                in
                             uu____14080 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14229  ->
                     let uu____14230 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14230);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14252 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14254::uu____14255 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14260) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14283 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14297 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14297
                              | uu____14308 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14312 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14338 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14356 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14373 =
                        let uu____14374 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14375 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14374 uu____14375
                         in
                      failwith uu____14373
                    else rebuild cfg env stack t2
                | uu____14377 -> norm cfg env stack t2))

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
                let uu____14387 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14387  in
              let uu____14388 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14388 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14401  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((true ,uu____14408),uu____14409);
                           FStar_Syntax_Syntax.sigrng = uu____14410;
                           FStar_Syntax_Syntax.sigquals = uu____14411;
                           FStar_Syntax_Syntax.sigmeta = uu____14412;
                           FStar_Syntax_Syntax.sigattrs = uu____14413;_},uu____14414),uu____14415)
                       when Prims.op_Negation (cfg.steps).zeta ->
                       rebuild cfg env stack t0
                   | uu____14480 ->
                       (log cfg
                          (fun uu____14485  ->
                             let uu____14486 =
                               FStar_Syntax_Print.term_to_string t0  in
                             let uu____14487 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____14486 uu____14487);
                        (let t1 =
                           if
                             ((cfg.steps).unfold_until =
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Delta_constant))
                               && (Prims.op_Negation (cfg.steps).unfold_tac)
                           then t
                           else
                             (let uu____14492 =
                                FStar_Ident.range_of_lid
                                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                 in
                              FStar_Syntax_Subst.set_use_range uu____14492 t)
                            in
                         let n1 = FStar_List.length us  in
                         if n1 > (Prims.parse_int "0")
                         then
                           match stack with
                           | (UnivArgs (us',uu____14501))::stack1 ->
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
                           | uu____14556 when
                               (cfg.steps).erase_universes ||
                                 (cfg.steps).allow_unbound_universes
                               -> norm cfg env stack t1
                           | uu____14559 ->
                               let uu____14562 =
                                 let uu____14563 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____14563
                                  in
                               failwith uu____14562
                         else norm cfg env stack t1)))

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
                  let uu___171_14587 = cfg  in
                  let uu____14588 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____14588;
                    tcenv = (uu___171_14587.tcenv);
                    debug = (uu___171_14587.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_14587.primitive_steps);
                    strong = (uu___171_14587.strong);
                    memoize_lazy = (uu___171_14587.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_14587.normalize_pure_lets)
                  }
                else
                  (let uu___172_14590 = cfg  in
                   {
                     steps =
                       (let uu___173_14593 = cfg.steps  in
                        {
                          beta = (uu___173_14593.beta);
                          iota = (uu___173_14593.iota);
                          zeta = false;
                          weak = (uu___173_14593.weak);
                          hnf = (uu___173_14593.hnf);
                          primops = (uu___173_14593.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_14593.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_14593.unfold_until);
                          unfold_only = (uu___173_14593.unfold_only);
                          unfold_fully = (uu___173_14593.unfold_fully);
                          unfold_attr = (uu___173_14593.unfold_attr);
                          unfold_tac = (uu___173_14593.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_14593.pure_subterms_within_computations);
                          simplify = (uu___173_14593.simplify);
                          erase_universes = (uu___173_14593.erase_universes);
                          allow_unbound_universes =
                            (uu___173_14593.allow_unbound_universes);
                          reify_ = (uu___173_14593.reify_);
                          compress_uvars = (uu___173_14593.compress_uvars);
                          no_full_norm = (uu___173_14593.no_full_norm);
                          check_no_uvars = (uu___173_14593.check_no_uvars);
                          unmeta = (uu___173_14593.unmeta);
                          unascribe = (uu___173_14593.unascribe);
                          in_full_norm_request =
                            (uu___173_14593.in_full_norm_request)
                        });
                     tcenv = (uu___172_14590.tcenv);
                     debug = (uu___172_14590.debug);
                     delta_level = (uu___172_14590.delta_level);
                     primitive_steps = (uu___172_14590.primitive_steps);
                     strong = (uu___172_14590.strong);
                     memoize_lazy = (uu___172_14590.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_14590.normalize_pure_lets)
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
                  (fun uu____14623  ->
                     let uu____14624 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____14625 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14624
                       uu____14625);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____14627 =
                   let uu____14628 = FStar_Syntax_Subst.compress head3  in
                   uu____14628.FStar_Syntax_Syntax.n  in
                 match uu____14627 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____14646 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14646
                        in
                     let uu____14647 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14647 with
                      | (uu____14648,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14654 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14662 =
                                   let uu____14663 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____14663.FStar_Syntax_Syntax.n  in
                                 match uu____14662 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14669,uu____14670))
                                     ->
                                     let uu____14679 =
                                       let uu____14680 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____14680.FStar_Syntax_Syntax.n  in
                                     (match uu____14679 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14686,msrc,uu____14688))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14697 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14697
                                      | uu____14698 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14699 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14700 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14700 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_14705 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_14705.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_14705.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_14705.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_14705.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_14705.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14706 = FStar_List.tl stack  in
                                    let uu____14707 =
                                      let uu____14708 =
                                        let uu____14711 =
                                          let uu____14712 =
                                            let uu____14725 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14725)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14712
                                           in
                                        FStar_Syntax_Syntax.mk uu____14711
                                         in
                                      uu____14708
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14706 uu____14707
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14741 =
                                      let uu____14742 = is_return body  in
                                      match uu____14742 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14746;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14747;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14752 -> false  in
                                    if uu____14741
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head3.FStar_Syntax_Syntax.pos  in
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
                                         let uu____14775 =
                                           let uu____14778 =
                                             let uu____14779 =
                                               let uu____14796 =
                                                 let uu____14799 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14799]  in
                                               (uu____14796, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14779
                                              in
                                           FStar_Syntax_Syntax.mk uu____14778
                                            in
                                         uu____14775
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14815 =
                                           let uu____14816 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14816.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14815 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14822::uu____14823::[])
                                             ->
                                             let uu____14830 =
                                               let uu____14833 =
                                                 let uu____14834 =
                                                   let uu____14841 =
                                                     let uu____14844 =
                                                       let uu____14845 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14845
                                                        in
                                                     let uu____14846 =
                                                       let uu____14849 =
                                                         let uu____14850 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14850
                                                          in
                                                       [uu____14849]  in
                                                     uu____14844 ::
                                                       uu____14846
                                                      in
                                                   (bind1, uu____14841)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14834
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14833
                                                in
                                             uu____14830
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14858 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14864 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14864
                                         then
                                           let uu____14867 =
                                             let uu____14868 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14868
                                              in
                                           let uu____14869 =
                                             let uu____14872 =
                                               let uu____14873 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14873
                                                in
                                             [uu____14872]  in
                                           uu____14867 :: uu____14869
                                         else []  in
                                       let reified =
                                         let uu____14878 =
                                           let uu____14881 =
                                             let uu____14882 =
                                               let uu____14897 =
                                                 let uu____14900 =
                                                   let uu____14903 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14904 =
                                                     let uu____14907 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14907]  in
                                                   uu____14903 :: uu____14904
                                                    in
                                                 let uu____14908 =
                                                   let uu____14911 =
                                                     let uu____14914 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14915 =
                                                       let uu____14918 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14919 =
                                                         let uu____14922 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14923 =
                                                           let uu____14926 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14926]  in
                                                         uu____14922 ::
                                                           uu____14923
                                                          in
                                                       uu____14918 ::
                                                         uu____14919
                                                        in
                                                     uu____14914 ::
                                                       uu____14915
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14911
                                                    in
                                                 FStar_List.append
                                                   uu____14900 uu____14908
                                                  in
                                               (bind_inst, uu____14897)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14882
                                              in
                                           FStar_Syntax_Syntax.mk uu____14881
                                            in
                                         uu____14878
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14938  ->
                                            let uu____14939 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14940 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14939 uu____14940);
                                       (let uu____14941 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14941 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14965 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14965
                        in
                     let uu____14966 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14966 with
                      | (uu____14967,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15002 =
                                  let uu____15003 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15003.FStar_Syntax_Syntax.n  in
                                match uu____15002 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15009) -> t2
                                | uu____15014 -> head4  in
                              let uu____15015 =
                                let uu____15016 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15016.FStar_Syntax_Syntax.n  in
                              match uu____15015 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15022 -> FStar_Pervasives_Native.None
                               in
                            let uu____15023 = maybe_extract_fv head4  in
                            match uu____15023 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15033 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15033
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____15038 = maybe_extract_fv head5
                                     in
                                  match uu____15038 with
                                  | FStar_Pervasives_Native.Some uu____15043
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15044 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____15049 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15064 =
                              match uu____15064 with
                              | (e,q) ->
                                  let uu____15071 =
                                    let uu____15072 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15072.FStar_Syntax_Syntax.n  in
                                  (match uu____15071 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____15087 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____15087
                                   | uu____15088 -> false)
                               in
                            let uu____15089 =
                              let uu____15090 =
                                let uu____15097 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15097 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15090
                               in
                            if uu____15089
                            then
                              let uu____15102 =
                                let uu____15103 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15103
                                 in
                              failwith uu____15102
                            else ());
                           (let uu____15105 = maybe_unfold_action head_app
                               in
                            match uu____15105 with
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
                                (log cfg
                                   (fun uu____15146  ->
                                      let uu____15147 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15148 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15147 uu____15148);
                                 (let uu____15149 = FStar_List.tl stack  in
                                  norm cfg env uu____15149 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15151) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15175 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15175  in
                     (log cfg
                        (fun uu____15179  ->
                           let uu____15180 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15180);
                      (let uu____15181 = FStar_List.tl stack  in
                       norm cfg env uu____15181 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15302  ->
                               match uu____15302 with
                               | (pat,wopt,tm) ->
                                   let uu____15350 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15350)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15382 = FStar_List.tl stack  in
                     norm cfg env uu____15382 tm
                 | uu____15383 -> fallback ())

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
              (fun uu____15397  ->
                 let uu____15398 = FStar_Ident.string_of_lid msrc  in
                 let uu____15399 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15400 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15398
                   uu____15399 uu____15400);
            (let uu____15401 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15401
             then
               let ed =
                 let uu____15403 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15403  in
               let uu____15404 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15404 with
               | (uu____15405,return_repr) ->
                   let return_inst =
                     let uu____15414 =
                       let uu____15415 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15415.FStar_Syntax_Syntax.n  in
                     match uu____15414 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15421::[]) ->
                         let uu____15428 =
                           let uu____15431 =
                             let uu____15432 =
                               let uu____15439 =
                                 let uu____15442 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15442]  in
                               (return_tm, uu____15439)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15432  in
                           FStar_Syntax_Syntax.mk uu____15431  in
                         uu____15428 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15450 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15453 =
                     let uu____15456 =
                       let uu____15457 =
                         let uu____15472 =
                           let uu____15475 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15476 =
                             let uu____15479 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15479]  in
                           uu____15475 :: uu____15476  in
                         (return_inst, uu____15472)  in
                       FStar_Syntax_Syntax.Tm_app uu____15457  in
                     FStar_Syntax_Syntax.mk uu____15456  in
                   uu____15453 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15488 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15488 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15491 =
                      let uu____15492 = FStar_Ident.text_of_lid msrc  in
                      let uu____15493 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15492 uu____15493
                       in
                    failwith uu____15491
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15494;
                      FStar_TypeChecker_Env.mtarget = uu____15495;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15496;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15511 =
                      let uu____15512 = FStar_Ident.text_of_lid msrc  in
                      let uu____15513 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15512 uu____15513
                       in
                    failwith uu____15511
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15514;
                      FStar_TypeChecker_Env.mtarget = uu____15515;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15516;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15540 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15541 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15540 t FStar_Syntax_Syntax.tun uu____15541))

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
                (fun uu____15597  ->
                   match uu____15597 with
                   | (a,imp) ->
                       let uu____15608 = norm cfg env [] a  in
                       (uu____15608, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____15616  ->
             let uu____15617 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____15618 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____15617 uu____15618);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15642 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                     uu____15642
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_15645 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_15645.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_15645.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15665 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____15665
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_15668 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_15668.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_15668.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15701  ->
                      match uu____15701 with
                      | (a,i) ->
                          let uu____15712 = norm cfg env [] a  in
                          (uu____15712, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_15730  ->
                       match uu___90_15730 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15734 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15734
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_15742 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_15745 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_15745.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_15742.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_15742.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15748  ->
        match uu____15748 with
        | (x,imp) ->
            let uu____15751 =
              let uu___179_15752 = x  in
              let uu____15753 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_15752.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_15752.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15753
              }  in
            (uu____15751, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15759 =
          FStar_List.fold_left
            (fun uu____15777  ->
               fun b  ->
                 match uu____15777 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15759 with | (nbs,uu____15817) -> FStar_List.rev nbs

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
            let uu____15833 =
              let uu___180_15834 = rc  in
              let uu____15835 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_15834.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15835;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_15834.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15833
        | uu____15842 -> lopt

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
          if (cfg.debug).b380
          then
            (let uu____15863 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15864 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15863
               uu____15864)
          else ();
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
          let uu____15884 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15884
          then tm1
          else
            (let w t =
               let uu___181_15896 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_15896.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_15896.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15905 =
                 let uu____15906 = FStar_Syntax_Util.unmeta t  in
                 uu____15906.FStar_Syntax_Syntax.n  in
               match uu____15905 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15913 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15958)::args1,(bv,uu____15961)::bs1) ->
                   let uu____15995 =
                     let uu____15996 = FStar_Syntax_Subst.compress t  in
                     uu____15996.FStar_Syntax_Syntax.n  in
                   (match uu____15995 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16000 -> false)
               | ([],[]) -> true
               | (uu____16021,uu____16022) -> false  in
             let is_applied bs t =
               let uu____16058 = FStar_Syntax_Util.head_and_args' t  in
               match uu____16058 with
               | (hd1,args) ->
                   let uu____16091 =
                     let uu____16092 = FStar_Syntax_Subst.compress hd1  in
                     uu____16092.FStar_Syntax_Syntax.n  in
                   (match uu____16091 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____16098 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____16110 = FStar_Syntax_Util.is_squash t  in
               match uu____16110 with
               | FStar_Pervasives_Native.Some (uu____16121,t') ->
                   is_applied bs t'
               | uu____16133 ->
                   let uu____16142 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____16142 with
                    | FStar_Pervasives_Native.Some (uu____16153,t') ->
                        is_applied bs t'
                    | uu____16165 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____16182 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16182 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16189)::(q,uu____16191)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____16226 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____16226 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____16231 =
                          let uu____16232 = FStar_Syntax_Subst.compress p  in
                          uu____16232.FStar_Syntax_Syntax.n  in
                        (match uu____16231 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16238 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____16238
                         | uu____16239 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____16242)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____16267 =
                          let uu____16268 = FStar_Syntax_Subst.compress p1
                             in
                          uu____16268.FStar_Syntax_Syntax.n  in
                        (match uu____16267 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16274 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____16274
                         | uu____16275 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____16279 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____16279 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____16284 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____16284 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16291 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16291
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____16294)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16319 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____16319 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16326 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16326
                              | uu____16327 -> FStar_Pervasives_Native.None)
                         | uu____16330 -> FStar_Pervasives_Native.None)
                    | uu____16333 -> FStar_Pervasives_Native.None)
               | uu____16336 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16347 =
                 let uu____16348 = FStar_Syntax_Subst.compress phi  in
                 uu____16348.FStar_Syntax_Syntax.n  in
               match uu____16347 with
               | FStar_Syntax_Syntax.Tm_match (uu____16353,br::brs) ->
                   let uu____16420 = br  in
                   (match uu____16420 with
                    | (uu____16437,uu____16438,e) ->
                        let r =
                          let uu____16459 = simp_t e  in
                          match uu____16459 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16465 =
                                FStar_List.for_all
                                  (fun uu____16483  ->
                                     match uu____16483 with
                                     | (uu____16496,uu____16497,e') ->
                                         let uu____16511 = simp_t e'  in
                                         uu____16511 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16465
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16519 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16524 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16524
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16545 =
                 match uu____16545 with
                 | (t1,q) ->
                     let uu____16558 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____16558 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____16586 -> (t1, q))
                  in
               let uu____16595 = FStar_Syntax_Util.head_and_args t  in
               match uu____16595 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16657 =
                 let uu____16658 = FStar_Syntax_Util.unmeta ty  in
                 uu____16658.FStar_Syntax_Syntax.n  in
               match uu____16657 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16662) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16667,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16687 -> false  in
             let simplify1 arg =
               let uu____16710 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16710, arg)  in
             let uu____16719 = is_quantified_const tm1  in
             match uu____16719 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16723 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16723
             | FStar_Pervasives_Native.None  ->
                 let uu____16724 =
                   let uu____16725 = FStar_Syntax_Subst.compress tm1  in
                   uu____16725.FStar_Syntax_Syntax.n  in
                 (match uu____16724 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16729;
                              FStar_Syntax_Syntax.vars = uu____16730;_},uu____16731);
                         FStar_Syntax_Syntax.pos = uu____16732;
                         FStar_Syntax_Syntax.vars = uu____16733;_},args)
                      ->
                      let uu____16759 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16759
                      then
                        let uu____16760 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16760 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16807)::
                             (uu____16808,(arg,uu____16810))::[] ->
                             maybe_auto_squash arg
                         | (uu____16859,(arg,uu____16861))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16862)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16911)::uu____16912::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16963::(FStar_Pervasives_Native.Some (false
                                         ),uu____16964)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17015 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17029 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17029
                         then
                           let uu____17030 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17030 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17077)::uu____17078::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17129::(FStar_Pervasives_Native.Some (true
                                           ),uu____17130)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17181)::(uu____17182,(arg,uu____17184))::[]
                               -> maybe_auto_squash arg
                           | (uu____17233,(arg,uu____17235))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17236)::[]
                               -> maybe_auto_squash arg
                           | uu____17285 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17299 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17299
                            then
                              let uu____17300 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17300 with
                              | uu____17347::(FStar_Pervasives_Native.Some
                                              (true ),uu____17348)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17399)::uu____17400::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17451)::(uu____17452,(arg,uu____17454))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17503,(p,uu____17505))::(uu____17506,
                                                                (q,uu____17508))::[]
                                  ->
                                  let uu____17555 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17555
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17557 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17571 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17571
                               then
                                 let uu____17572 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17572 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17619)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17620)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17671)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17672)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17723)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17724)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17775)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17776)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17827,(arg,uu____17829))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17830)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17879)::(uu____17880,(arg,uu____17882))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17931,(arg,uu____17933))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17934)::[]
                                     ->
                                     let uu____17983 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17983
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17984)::(uu____17985,(arg,uu____17987))::[]
                                     ->
                                     let uu____18036 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18036
                                 | (uu____18037,(p,uu____18039))::(uu____18040,
                                                                   (q,uu____18042))::[]
                                     ->
                                     let uu____18089 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18089
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18091 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18105 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18105
                                  then
                                    let uu____18106 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18106 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18153)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18184)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18215 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18229 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18229
                                     then
                                       match args with
                                       | (t,uu____18231)::[] ->
                                           let uu____18248 =
                                             let uu____18249 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18249.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18248 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18252::[],body,uu____18254)
                                                ->
                                                let uu____18281 = simp_t body
                                                   in
                                                (match uu____18281 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18284 -> tm1)
                                            | uu____18287 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18289))::(t,uu____18291)::[]
                                           ->
                                           let uu____18330 =
                                             let uu____18331 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18331.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18330 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18334::[],body,uu____18336)
                                                ->
                                                let uu____18363 = simp_t body
                                                   in
                                                (match uu____18363 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18366 -> tm1)
                                            | uu____18369 -> tm1)
                                       | uu____18370 -> tm1
                                     else
                                       (let uu____18380 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18380
                                        then
                                          match args with
                                          | (t,uu____18382)::[] ->
                                              let uu____18399 =
                                                let uu____18400 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18400.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18399 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18403::[],body,uu____18405)
                                                   ->
                                                   let uu____18432 =
                                                     simp_t body  in
                                                   (match uu____18432 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18435 -> tm1)
                                               | uu____18438 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18440))::(t,uu____18442)::[]
                                              ->
                                              let uu____18481 =
                                                let uu____18482 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18482.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18481 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18485::[],body,uu____18487)
                                                   ->
                                                   let uu____18514 =
                                                     simp_t body  in
                                                   (match uu____18514 with
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
                                                    | uu____18517 -> tm1)
                                               | uu____18520 -> tm1)
                                          | uu____18521 -> tm1
                                        else
                                          (let uu____18531 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18531
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18532;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18533;_},uu____18534)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18551;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18552;_},uu____18553)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18570 -> tm1
                                           else
                                             (let uu____18580 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18580 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18600 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18610;
                         FStar_Syntax_Syntax.vars = uu____18611;_},args)
                      ->
                      let uu____18633 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18633
                      then
                        let uu____18634 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18634 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18681)::
                             (uu____18682,(arg,uu____18684))::[] ->
                             maybe_auto_squash arg
                         | (uu____18733,(arg,uu____18735))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18736)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18785)::uu____18786::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18837::(FStar_Pervasives_Native.Some (false
                                         ),uu____18838)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18889 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18903 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18903
                         then
                           let uu____18904 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18904 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18951)::uu____18952::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19003::(FStar_Pervasives_Native.Some (true
                                           ),uu____19004)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19055)::(uu____19056,(arg,uu____19058))::[]
                               -> maybe_auto_squash arg
                           | (uu____19107,(arg,uu____19109))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19110)::[]
                               -> maybe_auto_squash arg
                           | uu____19159 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19173 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19173
                            then
                              let uu____19174 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19174 with
                              | uu____19221::(FStar_Pervasives_Native.Some
                                              (true ),uu____19222)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19273)::uu____19274::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19325)::(uu____19326,(arg,uu____19328))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19377,(p,uu____19379))::(uu____19380,
                                                                (q,uu____19382))::[]
                                  ->
                                  let uu____19429 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19429
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19431 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19445 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19445
                               then
                                 let uu____19446 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19446 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19493)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19494)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19545)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19546)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19597)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19598)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19649)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19650)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19701,(arg,uu____19703))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19704)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19753)::(uu____19754,(arg,uu____19756))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19805,(arg,uu____19807))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19808)::[]
                                     ->
                                     let uu____19857 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19857
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19858)::(uu____19859,(arg,uu____19861))::[]
                                     ->
                                     let uu____19910 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19910
                                 | (uu____19911,(p,uu____19913))::(uu____19914,
                                                                   (q,uu____19916))::[]
                                     ->
                                     let uu____19963 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19963
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19965 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19979 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19979
                                  then
                                    let uu____19980 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19980 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20027)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20058)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20089 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20103 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20103
                                     then
                                       match args with
                                       | (t,uu____20105)::[] ->
                                           let uu____20122 =
                                             let uu____20123 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20123.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20122 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20126::[],body,uu____20128)
                                                ->
                                                let uu____20155 = simp_t body
                                                   in
                                                (match uu____20155 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20158 -> tm1)
                                            | uu____20161 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20163))::(t,uu____20165)::[]
                                           ->
                                           let uu____20204 =
                                             let uu____20205 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20205.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20204 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20208::[],body,uu____20210)
                                                ->
                                                let uu____20237 = simp_t body
                                                   in
                                                (match uu____20237 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20240 -> tm1)
                                            | uu____20243 -> tm1)
                                       | uu____20244 -> tm1
                                     else
                                       (let uu____20254 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20254
                                        then
                                          match args with
                                          | (t,uu____20256)::[] ->
                                              let uu____20273 =
                                                let uu____20274 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20274.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20273 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20277::[],body,uu____20279)
                                                   ->
                                                   let uu____20306 =
                                                     simp_t body  in
                                                   (match uu____20306 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20309 -> tm1)
                                               | uu____20312 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20314))::(t,uu____20316)::[]
                                              ->
                                              let uu____20355 =
                                                let uu____20356 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20356.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20355 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20359::[],body,uu____20361)
                                                   ->
                                                   let uu____20388 =
                                                     simp_t body  in
                                                   (match uu____20388 with
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
                                                    | uu____20391 -> tm1)
                                               | uu____20394 -> tm1)
                                          | uu____20395 -> tm1
                                        else
                                          (let uu____20405 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20405
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20406;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20407;_},uu____20408)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20425;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20426;_},uu____20427)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20444 -> tm1
                                           else
                                             (let uu____20454 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20454 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20474 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20489 = simp_t t  in
                      (match uu____20489 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20492 ->
                      let uu____20515 = is_const_match tm1  in
                      (match uu____20515 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20518 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20529  ->
               let uu____20530 = FStar_Syntax_Print.tag_of_term t  in
               let uu____20531 = FStar_Syntax_Print.term_to_string t  in
               let uu____20532 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____20539 =
                 let uu____20540 =
                   let uu____20543 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____20543
                    in
                 stack_to_string uu____20540  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____20530 uu____20531 uu____20532 uu____20539);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20574 =
                     let uu____20575 =
                       let uu____20576 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20576  in
                     FStar_Util.string_of_int uu____20575  in
                   let uu____20581 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20582 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20574 uu____20581 uu____20582)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20588,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20637  ->
                     let uu____20638 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20638);
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
               let uu____20674 =
                 let uu___182_20675 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_20675.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_20675.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20674
           | (Arg (Univ uu____20676,uu____20677,uu____20678))::uu____20679 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20682,uu____20683))::uu____20684 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20699,uu____20700),aq,r))::stack1
               when
               let uu____20750 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20750 ->
               let t2 =
                 let uu____20754 =
                   let uu____20755 =
                     let uu____20756 = closure_as_term cfg env_arg tm  in
                     (uu____20756, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20755  in
                 uu____20754 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20762),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20815  ->
                     let uu____20816 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20816);
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
                  (let uu____20826 = FStar_ST.op_Bang m  in
                   match uu____20826 with
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
                   | FStar_Pervasives_Native.Some (uu____20963,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21010 =
                 log cfg
                   (fun uu____21014  ->
                      let uu____21015 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21015);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21019 =
                 let uu____21020 = FStar_Syntax_Subst.compress t1  in
                 uu____21020.FStar_Syntax_Syntax.n  in
               (match uu____21019 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21047 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21047  in
                    (log cfg
                       (fun uu____21051  ->
                          let uu____21052 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21052);
                     (let uu____21053 = FStar_List.tl stack  in
                      norm cfg env1 uu____21053 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21054);
                       FStar_Syntax_Syntax.pos = uu____21055;
                       FStar_Syntax_Syntax.vars = uu____21056;_},(e,uu____21058)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21087 when
                    (cfg.steps).primops ->
                    let uu____21102 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21102 with
                     | (hd1,args) ->
                         let uu____21139 =
                           let uu____21140 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21140.FStar_Syntax_Syntax.n  in
                         (match uu____21139 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21144 = find_prim_step cfg fv  in
                              (match uu____21144 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21147; arity = uu____21148;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21150;
                                     requires_binder_substitution =
                                       uu____21151;
                                     interpretation = uu____21152;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21165 -> fallback " (3)" ())
                          | uu____21168 -> fallback " (4)" ()))
                | uu____21169 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____21190  ->
                     let uu____21191 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21191);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21196 =
                   log cfg1
                     (fun uu____21201  ->
                        let uu____21202 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21203 =
                          let uu____21204 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21221  ->
                                    match uu____21221 with
                                    | (p,uu____21231,uu____21232) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21204
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21202 uu____21203);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_21249  ->
                                match uu___91_21249 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21250 -> false))
                         in
                      let steps =
                        let uu___183_21252 = cfg1.steps  in
                        {
                          beta = (uu___183_21252.beta);
                          iota = (uu___183_21252.iota);
                          zeta = false;
                          weak = (uu___183_21252.weak);
                          hnf = (uu___183_21252.hnf);
                          primops = (uu___183_21252.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_21252.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_21252.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_21252.pure_subterms_within_computations);
                          simplify = (uu___183_21252.simplify);
                          erase_universes = (uu___183_21252.erase_universes);
                          allow_unbound_universes =
                            (uu___183_21252.allow_unbound_universes);
                          reify_ = (uu___183_21252.reify_);
                          compress_uvars = (uu___183_21252.compress_uvars);
                          no_full_norm = (uu___183_21252.no_full_norm);
                          check_no_uvars = (uu___183_21252.check_no_uvars);
                          unmeta = (uu___183_21252.unmeta);
                          unascribe = (uu___183_21252.unascribe);
                          in_full_norm_request =
                            (uu___183_21252.in_full_norm_request)
                        }  in
                      let uu___184_21257 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_21257.tcenv);
                        debug = (uu___184_21257.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_21257.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_21257.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_21257.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      let uu____21265 =
                        whnf ||
                          ((FStar_Options.no_reduction_under_match ()) &&
                             (Prims.op_Negation
                                ((cfg1.steps).check_no_uvars ||
                                   (cfg1.steps).compress_uvars)))
                         in
                      if uu____21265
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21290 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21311 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21371  ->
                                    fun uu____21372  ->
                                      match (uu____21371, uu____21372) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21463 = norm_pat env3 p1
                                             in
                                          (match uu____21463 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21311 with
                           | (pats1,env3) ->
                               ((let uu___185_21545 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_21545.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_21564 = x  in
                            let uu____21565 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_21564.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_21564.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21565
                            }  in
                          ((let uu___187_21579 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_21579.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_21590 = x  in
                            let uu____21591 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_21590.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_21590.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21591
                            }  in
                          ((let uu___189_21605 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_21605.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_21621 = x  in
                            let uu____21622 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_21621.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_21621.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21622
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_21629 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_21629.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21639 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21653 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21653 with
                                  | (p,wopt,e) ->
                                      let uu____21673 = norm_pat env1 p  in
                                      (match uu____21673 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21698 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21698
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____21704 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____21704)
                    in
                 let rec is_cons head1 =
                   let uu____21709 =
                     let uu____21710 = FStar_Syntax_Subst.compress head1  in
                     uu____21710.FStar_Syntax_Syntax.n  in
                   match uu____21709 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21714) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21719 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21720;
                         FStar_Syntax_Syntax.fv_delta = uu____21721;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21722;
                         FStar_Syntax_Syntax.fv_delta = uu____21723;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21724);_}
                       -> true
                   | uu____21731 -> false  in
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
                   let uu____21876 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21876 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21963 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22002 ->
                                 let uu____22003 =
                                   let uu____22004 = is_cons head1  in
                                   Prims.op_Negation uu____22004  in
                                 FStar_Util.Inr uu____22003)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22029 =
                              let uu____22030 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22030.FStar_Syntax_Syntax.n  in
                            (match uu____22029 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22048 ->
                                 let uu____22049 =
                                   let uu____22050 = is_cons head1  in
                                   Prims.op_Negation uu____22050  in
                                 FStar_Util.Inr uu____22049))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22119)::rest_a,(p1,uu____22122)::rest_p) ->
                       let uu____22166 = matches_pat t2 p1  in
                       (match uu____22166 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22215 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22321 = matches_pat scrutinee1 p1  in
                       (match uu____22321 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____22361  ->
                                  let uu____22362 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22363 =
                                    let uu____22364 =
                                      FStar_List.map
                                        (fun uu____22374  ->
                                           match uu____22374 with
                                           | (uu____22379,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22364
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22362 uu____22363);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22410  ->
                                       match uu____22410 with
                                       | (bv,t2) ->
                                           let uu____22433 =
                                             let uu____22440 =
                                               let uu____22443 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22443
                                                in
                                             let uu____22444 =
                                               let uu____22445 =
                                                 let uu____22476 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22476, false)
                                                  in
                                               Clos uu____22445  in
                                             (uu____22440, uu____22444)  in
                                           uu____22433 :: env2) env1 s
                                 in
                              let uu____22593 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____22593)))
                    in
                 if (cfg1.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____22616 =
      let uu____22619 = FStar_ST.op_Bang plugins  in p :: uu____22619  in
    FStar_ST.op_Colon_Equals plugins uu____22616  in
  let retrieve uu____22717 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22782  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22815  ->
                  match uu___92_22815 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22819 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22825 -> d  in
        let uu____22828 = to_fsteps s  in
        let uu____22829 =
          let uu____22830 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22831 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22832 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22833 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22834 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22830;
            primop = uu____22831;
            b380 = uu____22832;
            norm_delayed = uu____22833;
            print_normalized = uu____22834
          }  in
        let uu____22835 =
          let uu____22838 =
            let uu____22841 = retrieve_plugins ()  in
            FStar_List.append uu____22841 psteps  in
          add_steps built_in_primitive_steps uu____22838  in
        let uu____22844 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22846 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22846)
           in
        {
          steps = uu____22828;
          tcenv = e;
          debug = uu____22829;
          delta_level = d1;
          primitive_steps = uu____22835;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22844
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
      fun t  -> let uu____22904 = config s e  in norm_comp uu____22904 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22917 = config [] env  in norm_universe uu____22917 [] u
  
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
        let uu____22935 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22935  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22942 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___192_22961 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___192_22961.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___192_22961.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22968 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22968
          then
            let ct1 =
              let uu____22970 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22970 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22977 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22977
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___193_22981 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___193_22981.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___193_22981.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___193_22981.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___194_22983 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___194_22983.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___194_22983.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___194_22983.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___194_22983.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___195_22984 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___195_22984.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_22984.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22986 -> c
  
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
        let uu____22998 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22998  in
      let uu____23005 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23005
      then
        let uu____23006 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23006 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23012  ->
                 let uu____23013 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23013)
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
            ((let uu____23030 =
                let uu____23035 =
                  let uu____23036 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23036
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23035)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23030);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23047 = config [AllowUnboundUniverses] env  in
          norm_comp uu____23047 [] c
        with
        | e ->
            ((let uu____23060 =
                let uu____23065 =
                  let uu____23066 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23066
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23065)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23060);
             c)
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
                   let uu____23103 =
                     let uu____23104 =
                       let uu____23111 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____23111)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23104  in
                   mk uu____23103 t01.FStar_Syntax_Syntax.pos
               | uu____23116 -> t2)
          | uu____23117 -> t2  in
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
        let uu____23157 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23157 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23186 ->
                 let uu____23193 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23193 with
                  | (actuals,uu____23203,uu____23204) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23218 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23218 with
                         | (binders,args) ->
                             let uu____23235 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23235
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
      | uu____23243 ->
          let uu____23244 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23244 with
           | (head1,args) ->
               let uu____23281 =
                 let uu____23282 = FStar_Syntax_Subst.compress head1  in
                 uu____23282.FStar_Syntax_Syntax.n  in
               (match uu____23281 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23285,thead) ->
                    let uu____23311 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23311 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23353 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_23361 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_23361.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_23361.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_23361.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_23361.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_23361.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_23361.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_23361.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_23361.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_23361.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_23361.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_23361.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_23361.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_23361.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_23361.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_23361.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_23361.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_23361.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_23361.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___200_23361.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___200_23361.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___200_23361.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_23361.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_23361.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___200_23361.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___200_23361.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___200_23361.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___200_23361.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___200_23361.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___200_23361.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___200_23361.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___200_23361.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___200_23361.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___200_23361.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23353 with
                            | (uu____23362,ty,uu____23364) ->
                                eta_expand_with_type env t ty))
                | uu____23365 ->
                    let uu____23366 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_23374 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_23374.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_23374.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_23374.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_23374.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_23374.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_23374.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_23374.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_23374.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_23374.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_23374.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_23374.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_23374.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_23374.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_23374.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_23374.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_23374.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_23374.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_23374.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___201_23374.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___201_23374.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___201_23374.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_23374.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_23374.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___201_23374.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___201_23374.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___201_23374.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___201_23374.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___201_23374.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___201_23374.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___201_23374.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___201_23374.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___201_23374.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___201_23374.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23366 with
                     | (uu____23375,ty,uu____23377) ->
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
      let uu___202_23434 = x  in
      let uu____23435 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___202_23434.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___202_23434.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23435
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23438 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23463 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23464 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23465 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23466 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23473 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23474 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23475 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___203_23503 = rc  in
          let uu____23504 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23511 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___203_23503.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23504;
            FStar_Syntax_Syntax.residual_flags = uu____23511
          }  in
        let uu____23514 =
          let uu____23515 =
            let uu____23532 = elim_delayed_subst_binders bs  in
            let uu____23539 = elim_delayed_subst_term t2  in
            let uu____23540 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23532, uu____23539, uu____23540)  in
          FStar_Syntax_Syntax.Tm_abs uu____23515  in
        mk1 uu____23514
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23569 =
          let uu____23570 =
            let uu____23583 = elim_delayed_subst_binders bs  in
            let uu____23590 = elim_delayed_subst_comp c  in
            (uu____23583, uu____23590)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23570  in
        mk1 uu____23569
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23603 =
          let uu____23604 =
            let uu____23611 = elim_bv bv  in
            let uu____23612 = elim_delayed_subst_term phi  in
            (uu____23611, uu____23612)  in
          FStar_Syntax_Syntax.Tm_refine uu____23604  in
        mk1 uu____23603
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____23635 =
          let uu____23636 =
            let uu____23651 = elim_delayed_subst_term t2  in
            let uu____23652 = elim_delayed_subst_args args  in
            (uu____23651, uu____23652)  in
          FStar_Syntax_Syntax.Tm_app uu____23636  in
        mk1 uu____23635
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___204_23716 = p  in
              let uu____23717 =
                let uu____23718 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23718  in
              {
                FStar_Syntax_Syntax.v = uu____23717;
                FStar_Syntax_Syntax.p =
                  (uu___204_23716.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___205_23720 = p  in
              let uu____23721 =
                let uu____23722 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23722  in
              {
                FStar_Syntax_Syntax.v = uu____23721;
                FStar_Syntax_Syntax.p =
                  (uu___205_23720.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___206_23729 = p  in
              let uu____23730 =
                let uu____23731 =
                  let uu____23738 = elim_bv x  in
                  let uu____23739 = elim_delayed_subst_term t0  in
                  (uu____23738, uu____23739)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23731  in
              {
                FStar_Syntax_Syntax.v = uu____23730;
                FStar_Syntax_Syntax.p =
                  (uu___206_23729.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___207_23758 = p  in
              let uu____23759 =
                let uu____23760 =
                  let uu____23773 =
                    FStar_List.map
                      (fun uu____23796  ->
                         match uu____23796 with
                         | (x,b) ->
                             let uu____23809 = elim_pat x  in
                             (uu____23809, b)) pats
                     in
                  (fv, uu____23773)  in
                FStar_Syntax_Syntax.Pat_cons uu____23760  in
              {
                FStar_Syntax_Syntax.v = uu____23759;
                FStar_Syntax_Syntax.p =
                  (uu___207_23758.FStar_Syntax_Syntax.p)
              }
          | uu____23822 -> p  in
        let elim_branch uu____23844 =
          match uu____23844 with
          | (pat,wopt,t3) ->
              let uu____23870 = elim_pat pat  in
              let uu____23873 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23876 = elim_delayed_subst_term t3  in
              (uu____23870, uu____23873, uu____23876)
           in
        let uu____23881 =
          let uu____23882 =
            let uu____23905 = elim_delayed_subst_term t2  in
            let uu____23906 = FStar_List.map elim_branch branches  in
            (uu____23905, uu____23906)  in
          FStar_Syntax_Syntax.Tm_match uu____23882  in
        mk1 uu____23881
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24015 =
          match uu____24015 with
          | (tc,topt) ->
              let uu____24050 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24060 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24060
                | FStar_Util.Inr c ->
                    let uu____24062 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24062
                 in
              let uu____24063 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24050, uu____24063)
           in
        let uu____24072 =
          let uu____24073 =
            let uu____24100 = elim_delayed_subst_term t2  in
            let uu____24101 = elim_ascription a  in
            (uu____24100, uu____24101, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24073  in
        mk1 uu____24072
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___208_24146 = lb  in
          let uu____24147 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24150 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___208_24146.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___208_24146.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24147;
            FStar_Syntax_Syntax.lbeff =
              (uu___208_24146.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24150;
            FStar_Syntax_Syntax.lbattrs =
              (uu___208_24146.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___208_24146.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24153 =
          let uu____24154 =
            let uu____24167 =
              let uu____24174 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24174)  in
            let uu____24183 = elim_delayed_subst_term t2  in
            (uu____24167, uu____24183)  in
          FStar_Syntax_Syntax.Tm_let uu____24154  in
        mk1 uu____24153
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24216 =
          let uu____24217 =
            let uu____24234 = elim_delayed_subst_term t2  in
            (uv, uu____24234)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24217  in
        mk1 uu____24216
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24252 =
          let uu____24253 =
            let uu____24260 = elim_delayed_subst_term tm  in
            (uu____24260, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24253  in
        mk1 uu____24252
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24267 =
          let uu____24268 =
            let uu____24275 = elim_delayed_subst_term t2  in
            let uu____24276 = elim_delayed_subst_meta md  in
            (uu____24275, uu____24276)  in
          FStar_Syntax_Syntax.Tm_meta uu____24268  in
        mk1 uu____24267

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24283  ->
         match uu___93_24283 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24287 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24287
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
        let uu____24308 =
          let uu____24309 =
            let uu____24318 = elim_delayed_subst_term t  in
            (uu____24318, uopt)  in
          FStar_Syntax_Syntax.Total uu____24309  in
        mk1 uu____24308
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24331 =
          let uu____24332 =
            let uu____24341 = elim_delayed_subst_term t  in
            (uu____24341, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24332  in
        mk1 uu____24331
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___209_24346 = ct  in
          let uu____24347 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24350 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24359 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___209_24346.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___209_24346.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24347;
            FStar_Syntax_Syntax.effect_args = uu____24350;
            FStar_Syntax_Syntax.flags = uu____24359
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24362  ->
    match uu___94_24362 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24374 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24374
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24407 =
          let uu____24414 = elim_delayed_subst_term t  in (m, uu____24414)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24407
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24422 =
          let uu____24431 = elim_delayed_subst_term t  in
          (m1, m2, uu____24431)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24422
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24454  ->
         match uu____24454 with
         | (t,q) ->
             let uu____24465 = elim_delayed_subst_term t  in (uu____24465, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24485  ->
         match uu____24485 with
         | (x,q) ->
             let uu____24496 =
               let uu___210_24497 = x  in
               let uu____24498 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___210_24497.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___210_24497.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24498
               }  in
             (uu____24496, q)) bs

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
            | (uu____24574,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24580,FStar_Util.Inl t) ->
                let uu____24586 =
                  let uu____24589 =
                    let uu____24590 =
                      let uu____24603 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____24603)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____24590  in
                  FStar_Syntax_Syntax.mk uu____24589  in
                uu____24586 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____24607 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____24607 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____24635 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24690 ->
                    let uu____24691 =
                      let uu____24700 =
                        let uu____24701 = FStar_Syntax_Subst.compress t4  in
                        uu____24701.FStar_Syntax_Syntax.n  in
                      (uu____24700, tc)  in
                    (match uu____24691 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24726) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24763) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24802,FStar_Util.Inl uu____24803) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24826 -> failwith "Impossible")
                 in
              (match uu____24635 with
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
          let uu____24931 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24931 with
          | (univ_names1,binders1,tc) ->
              let uu____24989 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24989)
  
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
          let uu____25024 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25024 with
          | (univ_names1,binders1,tc) ->
              let uu____25084 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25084)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25117 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25117 with
           | (univ_names1,binders1,typ1) ->
               let uu___211_25145 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_25145.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_25145.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_25145.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_25145.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___212_25166 = s  in
          let uu____25167 =
            let uu____25168 =
              let uu____25177 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25177, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25168  in
          {
            FStar_Syntax_Syntax.sigel = uu____25167;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_25166.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_25166.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_25166.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_25166.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25194 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25194 with
           | (univ_names1,uu____25212,typ1) ->
               let uu___213_25226 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_25226.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_25226.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_25226.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_25226.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25232 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25232 with
           | (univ_names1,uu____25250,typ1) ->
               let uu___214_25264 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_25264.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_25264.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_25264.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_25264.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25298 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25298 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25321 =
                            let uu____25322 =
                              let uu____25323 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25323  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25322
                             in
                          elim_delayed_subst_term uu____25321  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___215_25326 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___215_25326.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_25326.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___215_25326.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___215_25326.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___216_25327 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___216_25327.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_25327.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_25327.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_25327.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___217_25339 = s  in
          let uu____25340 =
            let uu____25341 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25341  in
          {
            FStar_Syntax_Syntax.sigel = uu____25340;
            FStar_Syntax_Syntax.sigrng =
              (uu___217_25339.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_25339.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_25339.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_25339.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25345 = elim_uvars_aux_t env us [] t  in
          (match uu____25345 with
           | (us1,uu____25363,t1) ->
               let uu___218_25377 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_25377.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_25377.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_25377.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_25377.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25378 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25380 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25380 with
           | (univs1,binders,signature) ->
               let uu____25408 =
                 let uu____25417 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____25417 with
                 | (univs_opening,univs2) ->
                     let uu____25444 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25444)
                  in
               (match uu____25408 with
                | (univs_opening,univs_closing) ->
                    let uu____25461 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25467 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25468 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25467, uu____25468)  in
                    (match uu____25461 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____25490 =
                           match uu____25490 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____25508 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____25508 with
                                | (us1,t1) ->
                                    let uu____25519 =
                                      let uu____25524 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____25531 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____25524, uu____25531)  in
                                    (match uu____25519 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____25544 =
                                           let uu____25549 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____25558 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____25549, uu____25558)  in
                                         (match uu____25544 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25574 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25574
                                                 in
                                              let uu____25575 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____25575 with
                                               | (uu____25596,uu____25597,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____25612 =
                                                       let uu____25613 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25613
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25612
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____25618 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____25618 with
                           | (uu____25631,uu____25632,t1) -> t1  in
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
                             | uu____25692 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25709 =
                               let uu____25710 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25710.FStar_Syntax_Syntax.n  in
                             match uu____25709 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25769 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25798 =
                               let uu____25799 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25799.FStar_Syntax_Syntax.n  in
                             match uu____25798 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25820) ->
                                 let uu____25841 = destruct_action_body body
                                    in
                                 (match uu____25841 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25886 ->
                                 let uu____25887 = destruct_action_body t  in
                                 (match uu____25887 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25936 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25936 with
                           | (action_univs,t) ->
                               let uu____25945 = destruct_action_typ_templ t
                                  in
                               (match uu____25945 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___219_25986 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___219_25986.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___219_25986.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___220_25988 = ed  in
                           let uu____25989 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25990 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25991 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25992 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25993 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25994 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25995 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25996 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25997 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25998 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25999 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26000 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26001 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26002 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___220_25988.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___220_25988.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25989;
                             FStar_Syntax_Syntax.bind_wp = uu____25990;
                             FStar_Syntax_Syntax.if_then_else = uu____25991;
                             FStar_Syntax_Syntax.ite_wp = uu____25992;
                             FStar_Syntax_Syntax.stronger = uu____25993;
                             FStar_Syntax_Syntax.close_wp = uu____25994;
                             FStar_Syntax_Syntax.assert_p = uu____25995;
                             FStar_Syntax_Syntax.assume_p = uu____25996;
                             FStar_Syntax_Syntax.null_wp = uu____25997;
                             FStar_Syntax_Syntax.trivial = uu____25998;
                             FStar_Syntax_Syntax.repr = uu____25999;
                             FStar_Syntax_Syntax.return_repr = uu____26000;
                             FStar_Syntax_Syntax.bind_repr = uu____26001;
                             FStar_Syntax_Syntax.actions = uu____26002;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___220_25988.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___221_26005 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___221_26005.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___221_26005.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___221_26005.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___221_26005.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_26022 =
            match uu___95_26022 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26049 = elim_uvars_aux_t env us [] t  in
                (match uu____26049 with
                 | (us1,uu____26073,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___222_26092 = sub_eff  in
            let uu____26093 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26096 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___222_26092.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___222_26092.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26093;
              FStar_Syntax_Syntax.lift = uu____26096
            }  in
          let uu___223_26099 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___223_26099.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_26099.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_26099.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_26099.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26109 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26109 with
           | (univ_names1,binders1,comp1) ->
               let uu___224_26143 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_26143.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_26143.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_26143.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_26143.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26154 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26155 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  