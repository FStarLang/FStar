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
                         rebuild_closure cfg env0 stack t1)
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
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10021) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10031) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____10050  ->
                  match uu____10050 with
                  | (a,uu____10058) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10064 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____10089 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____10090 -> false
    | FStar_Syntax_Syntax.Tm_type uu____10107 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____10108 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____10109 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____10110 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____10111 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____10112 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____10119 -> false
    | FStar_Syntax_Syntax.Tm_let uu____10126 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____10139 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____10156 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____10169 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____10215  ->
                   match uu____10215 with
                   | (a,uu____10223) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right pats
             (FStar_Util.for_some
                (fun uu____10300  ->
                   match uu____10300 with
                   | (uu____10315,wopt,t2) ->
                       (match wopt with
                        | FStar_Pervasives_Native.None  -> false
                        | FStar_Pervasives_Native.Some t3 ->
                            maybe_weakly_reduced t3)
                         || (maybe_weakly_reduced t2))))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____10343) ->
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
                     (fun uu____10465  ->
                        match uu____10465 with
                        | (a,uu____10473) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____10478,uu____10479,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____10485,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____10491 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____10498 -> false
            | FStar_Syntax_Syntax.Meta_named uu____10499 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10681 ->
                   let uu____10706 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10706
               | uu____10707 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____10715  ->
               let uu____10716 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10717 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10718 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10725 =
                 let uu____10726 =
                   let uu____10729 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10729
                    in
                 stack_to_string uu____10726  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10716 uu____10717 uu____10718 uu____10725);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10752 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10753 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____10754 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10755;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10756;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10759;
                 FStar_Syntax_Syntax.fv_delta = uu____10760;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10761;
                 FStar_Syntax_Syntax.fv_delta = uu____10762;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10763);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____10770 ->
               let uu____10777 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____10777
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10807 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10807)
               ->
               let cfg' =
                 let uu___147_10809 = cfg  in
                 {
                   steps =
                     (let uu___148_10812 = cfg.steps  in
                      {
                        beta = (uu___148_10812.beta);
                        iota = (uu___148_10812.iota);
                        zeta = (uu___148_10812.zeta);
                        weak = (uu___148_10812.weak);
                        hnf = (uu___148_10812.hnf);
                        primops = (uu___148_10812.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_10812.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_10812.unfold_attr);
                        unfold_tac = (uu___148_10812.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_10812.pure_subterms_within_computations);
                        simplify = (uu___148_10812.simplify);
                        erase_universes = (uu___148_10812.erase_universes);
                        allow_unbound_universes =
                          (uu___148_10812.allow_unbound_universes);
                        reify_ = (uu___148_10812.reify_);
                        compress_uvars = (uu___148_10812.compress_uvars);
                        no_full_norm = (uu___148_10812.no_full_norm);
                        check_no_uvars = (uu___148_10812.check_no_uvars);
                        unmeta = (uu___148_10812.unmeta);
                        unascribe = (uu___148_10812.unascribe);
                        in_full_norm_request =
                          (uu___148_10812.in_full_norm_request)
                      });
                   tcenv = (uu___147_10809.tcenv);
                   debug = (uu___147_10809.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_10809.primitive_steps);
                   strong = (uu___147_10809.strong);
                   memoize_lazy = (uu___147_10809.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10817 = get_norm_request (norm cfg' env []) args  in
               (match uu____10817 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10848  ->
                              fun stack1  ->
                                match uu____10848 with
                                | (a,aq) ->
                                    let uu____10860 =
                                      let uu____10861 =
                                        let uu____10868 =
                                          let uu____10869 =
                                            let uu____10900 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10900, false)  in
                                          Clos uu____10869  in
                                        (uu____10868, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10861  in
                                    uu____10860 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10984  ->
                          let uu____10985 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10985);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____11007 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_11012  ->
                                match uu___88_11012 with
                                | UnfoldUntil uu____11013 -> true
                                | UnfoldOnly uu____11014 -> true
                                | UnfoldFully uu____11017 -> true
                                | uu____11020 -> false))
                         in
                      if uu____11007
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_11025 = cfg  in
                      let uu____11026 =
                        let uu___150_11027 = to_fsteps s  in
                        {
                          beta = (uu___150_11027.beta);
                          iota = (uu___150_11027.iota);
                          zeta = (uu___150_11027.zeta);
                          weak = (uu___150_11027.weak);
                          hnf = (uu___150_11027.hnf);
                          primops = (uu___150_11027.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_11027.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_11027.unfold_until);
                          unfold_only = (uu___150_11027.unfold_only);
                          unfold_fully = (uu___150_11027.unfold_fully);
                          unfold_attr = (uu___150_11027.unfold_attr);
                          unfold_tac = (uu___150_11027.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_11027.pure_subterms_within_computations);
                          simplify = (uu___150_11027.simplify);
                          erase_universes = (uu___150_11027.erase_universes);
                          allow_unbound_universes =
                            (uu___150_11027.allow_unbound_universes);
                          reify_ = (uu___150_11027.reify_);
                          compress_uvars = (uu___150_11027.compress_uvars);
                          no_full_norm = (uu___150_11027.no_full_norm);
                          check_no_uvars = (uu___150_11027.check_no_uvars);
                          unmeta = (uu___150_11027.unmeta);
                          unascribe = (uu___150_11027.unascribe);
                          in_full_norm_request = true
                        }  in
                      {
                        steps = uu____11026;
                        tcenv = (uu___149_11025.tcenv);
                        debug = (uu___149_11025.debug);
                        delta_level;
                        primitive_steps = (uu___149_11025.primitive_steps);
                        strong = (uu___149_11025.strong);
                        memoize_lazy = (uu___149_11025.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____11036 =
                          let uu____11037 =
                            let uu____11042 = FStar_Util.now ()  in
                            (t1, uu____11042)  in
                          Debug uu____11037  in
                        uu____11036 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11046 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11046
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11055 =
                      let uu____11062 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11062, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11055  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____11072 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____11072  in
               let uu____11073 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____11073
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____11079  ->
                       let uu____11080 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11081 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____11080 uu____11081);
                  if b
                  then
                    (let uu____11082 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____11082 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____11090 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____11090) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____11103),uu____11104);
                                FStar_Syntax_Syntax.sigrng = uu____11105;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____11107;
                                FStar_Syntax_Syntax.sigattrs = uu____11108;_},uu____11109),uu____11110)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____11175 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_11179  ->
                               match uu___89_11179 with
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
                          (let uu____11189 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____11189))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____11208) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____11243,uu____11244) -> false)))
                     in
                  let uu____11261 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____11277 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____11277 then (true, true) else (false, false)
                     in
                  match uu____11261 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____11290  ->
                            let uu____11291 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____11292 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____11293 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____11291 uu____11292 uu____11293);
                       if should_delta2
                       then
                         (let uu____11294 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_11310 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_11313 = cfg.steps  in
                                      {
                                        beta = (uu___152_11313.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_11313.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_11313.unfold_attr);
                                        unfold_tac =
                                          (uu___152_11313.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_11313.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_11313.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_11313.allow_unbound_universes);
                                        reify_ = (uu___152_11313.reify_);
                                        compress_uvars =
                                          (uu___152_11313.compress_uvars);
                                        no_full_norm =
                                          (uu___152_11313.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_11313.check_no_uvars);
                                        unmeta = (uu___152_11313.unmeta);
                                        unascribe =
                                          (uu___152_11313.unascribe);
                                        in_full_norm_request =
                                          (uu___152_11313.in_full_norm_request)
                                      });
                                   tcenv = (uu___151_11310.tcenv);
                                   debug = (uu___151_11310.debug);
                                   delta_level = (uu___151_11310.delta_level);
                                   primitive_steps =
                                     (uu___151_11310.primitive_steps);
                                   strong = (uu___151_11310.strong);
                                   memoize_lazy =
                                     (uu___151_11310.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_11310.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____11294 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11327 = lookup_bvar env x  in
               (match uu____11327 with
                | Univ uu____11328 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____11377 = FStar_ST.op_Bang r  in
                      (match uu____11377 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11495  ->
                                 let uu____11496 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11497 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11496
                                   uu____11497);
                            (let uu____11498 = maybe_weakly_reduced t'  in
                             if uu____11498
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____11499 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11570)::uu____11571 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11580)::uu____11581 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11593,uu____11594))::stack_rest ->
                    (match c with
                     | Univ uu____11598 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11607 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11628  ->
                                    let uu____11629 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11629);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11669  ->
                                    let uu____11670 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11670);
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
                       (fun uu____11748  ->
                          let uu____11749 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11749);
                     norm cfg env stack1 t1)
                | (Debug uu____11750)::uu____11751 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11761 = cfg.steps  in
                             {
                               beta = (uu___153_11761.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11761.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11761.unfold_until);
                               unfold_only = (uu___153_11761.unfold_only);
                               unfold_fully = (uu___153_11761.unfold_fully);
                               unfold_attr = (uu___153_11761.unfold_attr);
                               unfold_tac = (uu___153_11761.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11761.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11761.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11761.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11761.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11761.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11763 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11763.tcenv);
                               debug = (uu___154_11763.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11763.primitive_steps);
                               strong = (uu___154_11763.strong);
                               memoize_lazy = (uu___154_11763.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11763.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11765 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11765 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11807  -> dummy :: env1) env)
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
                                          let uu____11844 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11844)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11849 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11849.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11849.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11850 -> lopt  in
                           (log cfg
                              (fun uu____11856  ->
                                 let uu____11857 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11857);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11866 = cfg  in
                               {
                                 steps = (uu___156_11866.steps);
                                 tcenv = (uu___156_11866.tcenv);
                                 debug = (uu___156_11866.debug);
                                 delta_level = (uu___156_11866.delta_level);
                                 primitive_steps =
                                   (uu___156_11866.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11866.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11866.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11877)::uu____11878 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11890 = cfg.steps  in
                             {
                               beta = (uu___153_11890.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11890.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11890.unfold_until);
                               unfold_only = (uu___153_11890.unfold_only);
                               unfold_fully = (uu___153_11890.unfold_fully);
                               unfold_attr = (uu___153_11890.unfold_attr);
                               unfold_tac = (uu___153_11890.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11890.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11890.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11890.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11890.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11890.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11892 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11892.tcenv);
                               debug = (uu___154_11892.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11892.primitive_steps);
                               strong = (uu___154_11892.strong);
                               memoize_lazy = (uu___154_11892.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11892.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11894 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11894 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11936  -> dummy :: env1) env)
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
                                          let uu____11973 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11973)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11978 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11978.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11978.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11979 -> lopt  in
                           (log cfg
                              (fun uu____11985  ->
                                 let uu____11986 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11986);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11995 = cfg  in
                               {
                                 steps = (uu___156_11995.steps);
                                 tcenv = (uu___156_11995.tcenv);
                                 debug = (uu___156_11995.debug);
                                 delta_level = (uu___156_11995.delta_level);
                                 primitive_steps =
                                   (uu___156_11995.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11995.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11995.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12006)::uu____12007 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12021 = cfg.steps  in
                             {
                               beta = (uu___153_12021.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12021.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12021.unfold_until);
                               unfold_only = (uu___153_12021.unfold_only);
                               unfold_fully = (uu___153_12021.unfold_fully);
                               unfold_attr = (uu___153_12021.unfold_attr);
                               unfold_tac = (uu___153_12021.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12021.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12021.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12021.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12021.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12021.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_12023 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12023.tcenv);
                               debug = (uu___154_12023.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12023.primitive_steps);
                               strong = (uu___154_12023.strong);
                               memoize_lazy = (uu___154_12023.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12023.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12025 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12025 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12067  -> dummy :: env1) env)
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
                                          let uu____12104 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12104)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12109 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12109.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12109.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12110 -> lopt  in
                           (log cfg
                              (fun uu____12116  ->
                                 let uu____12117 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12117);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12126 = cfg  in
                               {
                                 steps = (uu___156_12126.steps);
                                 tcenv = (uu___156_12126.tcenv);
                                 debug = (uu___156_12126.debug);
                                 delta_level = (uu___156_12126.delta_level);
                                 primitive_steps =
                                   (uu___156_12126.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12126.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12126.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12137)::uu____12138 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12152 = cfg.steps  in
                             {
                               beta = (uu___153_12152.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12152.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12152.unfold_until);
                               unfold_only = (uu___153_12152.unfold_only);
                               unfold_fully = (uu___153_12152.unfold_fully);
                               unfold_attr = (uu___153_12152.unfold_attr);
                               unfold_tac = (uu___153_12152.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12152.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12152.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12152.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12152.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12152.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_12154 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12154.tcenv);
                               debug = (uu___154_12154.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12154.primitive_steps);
                               strong = (uu___154_12154.strong);
                               memoize_lazy = (uu___154_12154.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12154.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12156 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12156 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12198  -> dummy :: env1) env)
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
                                          let uu____12235 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12235)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12240 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12240.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12240.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12241 -> lopt  in
                           (log cfg
                              (fun uu____12247  ->
                                 let uu____12248 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12248);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12257 = cfg  in
                               {
                                 steps = (uu___156_12257.steps);
                                 tcenv = (uu___156_12257.tcenv);
                                 debug = (uu___156_12257.debug);
                                 delta_level = (uu___156_12257.delta_level);
                                 primitive_steps =
                                   (uu___156_12257.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12257.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12257.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12268)::uu____12269 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12287 = cfg.steps  in
                             {
                               beta = (uu___153_12287.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12287.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12287.unfold_until);
                               unfold_only = (uu___153_12287.unfold_only);
                               unfold_fully = (uu___153_12287.unfold_fully);
                               unfold_attr = (uu___153_12287.unfold_attr);
                               unfold_tac = (uu___153_12287.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12287.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12287.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12287.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12287.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12287.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_12289 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12289.tcenv);
                               debug = (uu___154_12289.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12289.primitive_steps);
                               strong = (uu___154_12289.strong);
                               memoize_lazy = (uu___154_12289.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12289.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12291 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12291 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12333  -> dummy :: env1) env)
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
                                          let uu____12370 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12370)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12375 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12375.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12375.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12376 -> lopt  in
                           (log cfg
                              (fun uu____12382  ->
                                 let uu____12383 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12383);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12392 = cfg  in
                               {
                                 steps = (uu___156_12392.steps);
                                 tcenv = (uu___156_12392.tcenv);
                                 debug = (uu___156_12392.debug);
                                 delta_level = (uu___156_12392.delta_level);
                                 primitive_steps =
                                   (uu___156_12392.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12392.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12392.normalize_pure_lets)
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
                             let uu___153_12406 = cfg.steps  in
                             {
                               beta = (uu___153_12406.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12406.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12406.unfold_until);
                               unfold_only = (uu___153_12406.unfold_only);
                               unfold_fully = (uu___153_12406.unfold_fully);
                               unfold_attr = (uu___153_12406.unfold_attr);
                               unfold_tac = (uu___153_12406.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12406.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12406.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12406.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12406.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12406.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_12408 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12408.tcenv);
                               debug = (uu___154_12408.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12408.primitive_steps);
                               strong = (uu___154_12408.strong);
                               memoize_lazy = (uu___154_12408.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12408.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12410 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12410 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12452  -> dummy :: env1) env)
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
                                          let uu____12489 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12489)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12494 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12494.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12494.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12495 -> lopt  in
                           (log cfg
                              (fun uu____12501  ->
                                 let uu____12502 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12502);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12511 = cfg  in
                               {
                                 steps = (uu___156_12511.steps);
                                 tcenv = (uu___156_12511.tcenv);
                                 debug = (uu___156_12511.debug);
                                 delta_level = (uu___156_12511.delta_level);
                                 primitive_steps =
                                   (uu___156_12511.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12511.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12511.normalize_pure_lets)
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
                      (fun uu____12560  ->
                         fun stack1  ->
                           match uu____12560 with
                           | (a,aq) ->
                               let uu____12572 =
                                 let uu____12573 =
                                   let uu____12580 =
                                     let uu____12581 =
                                       let uu____12612 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12612, false)  in
                                     Clos uu____12581  in
                                   (uu____12580, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12573  in
                               uu____12572 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12696  ->
                     let uu____12697 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12697);
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
                             ((let uu___157_12733 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12733.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12733.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12734 ->
                      let uu____12739 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12739)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12742 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12742 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12773 =
                          let uu____12774 =
                            let uu____12781 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_12783 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_12783.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_12783.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12781)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12774  in
                        mk uu____12773 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12802 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12802
               else
                 (let uu____12804 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12804 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12812 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12836  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12812 c1  in
                      let t2 =
                        let uu____12858 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12858 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12969)::uu____12970 ->
                    (log cfg
                       (fun uu____12983  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12984)::uu____12985 ->
                    (log cfg
                       (fun uu____12996  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12997,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12998;
                                   FStar_Syntax_Syntax.vars = uu____12999;_},uu____13000,uu____13001))::uu____13002
                    ->
                    (log cfg
                       (fun uu____13011  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13012)::uu____13013 ->
                    (log cfg
                       (fun uu____13024  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13025 ->
                    (log cfg
                       (fun uu____13028  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13032  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13049 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13049
                         | FStar_Util.Inr c ->
                             let uu____13057 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13057
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13070 =
                               let uu____13071 =
                                 let uu____13098 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13098, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13071
                                in
                             mk uu____13070 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____13117 ->
                           let uu____13118 =
                             let uu____13119 =
                               let uu____13120 =
                                 let uu____13147 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13147, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13120
                                in
                             mk uu____13119 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____13118))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if (cfg.steps).iota
                 then
                   let uu___159_13224 = cfg  in
                   {
                     steps =
                       (let uu___160_13227 = cfg.steps  in
                        {
                          beta = (uu___160_13227.beta);
                          iota = (uu___160_13227.iota);
                          zeta = (uu___160_13227.zeta);
                          weak = true;
                          hnf = (uu___160_13227.hnf);
                          primops = (uu___160_13227.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_13227.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_13227.unfold_until);
                          unfold_only = (uu___160_13227.unfold_only);
                          unfold_fully = (uu___160_13227.unfold_fully);
                          unfold_attr = (uu___160_13227.unfold_attr);
                          unfold_tac = (uu___160_13227.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_13227.pure_subterms_within_computations);
                          simplify = (uu___160_13227.simplify);
                          erase_universes = (uu___160_13227.erase_universes);
                          allow_unbound_universes =
                            (uu___160_13227.allow_unbound_universes);
                          reify_ = (uu___160_13227.reify_);
                          compress_uvars = (uu___160_13227.compress_uvars);
                          no_full_norm = (uu___160_13227.no_full_norm);
                          check_no_uvars = (uu___160_13227.check_no_uvars);
                          unmeta = (uu___160_13227.unmeta);
                          unascribe = (uu___160_13227.unascribe);
                          in_full_norm_request =
                            (uu___160_13227.in_full_norm_request)
                        });
                     tcenv = (uu___159_13224.tcenv);
                     debug = (uu___159_13224.debug);
                     delta_level = (uu___159_13224.delta_level);
                     primitive_steps = (uu___159_13224.primitive_steps);
                     strong = (uu___159_13224.strong);
                     memoize_lazy = (uu___159_13224.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_13224.normalize_pure_lets)
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
                         let uu____13263 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13263 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_13283 = cfg  in
                               let uu____13284 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_13283.steps);
                                 tcenv = uu____13284;
                                 debug = (uu___161_13283.debug);
                                 delta_level = (uu___161_13283.delta_level);
                                 primitive_steps =
                                   (uu___161_13283.primitive_steps);
                                 strong = (uu___161_13283.strong);
                                 memoize_lazy = (uu___161_13283.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_13283.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____13289 =
                                 let uu____13290 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13290  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13289
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_13293 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_13293.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_13293.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_13293.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_13293.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____13294 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13294
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13305,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13306;
                               FStar_Syntax_Syntax.lbunivs = uu____13307;
                               FStar_Syntax_Syntax.lbtyp = uu____13308;
                               FStar_Syntax_Syntax.lbeff = uu____13309;
                               FStar_Syntax_Syntax.lbdef = uu____13310;
                               FStar_Syntax_Syntax.lbattrs = uu____13311;
                               FStar_Syntax_Syntax.lbpos = uu____13312;_}::uu____13313),uu____13314)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13354 =
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
               if uu____13354
               then
                 let binder =
                   let uu____13356 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13356  in
                 let env1 =
                   let uu____13366 =
                     let uu____13373 =
                       let uu____13374 =
                         let uu____13405 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13405,
                           false)
                          in
                       Clos uu____13374  in
                     ((FStar_Pervasives_Native.Some binder), uu____13373)  in
                   uu____13366 :: env  in
                 (log cfg
                    (fun uu____13498  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____13502  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13503 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13503))
                 else
                   (let uu____13505 =
                      let uu____13510 =
                        let uu____13511 =
                          let uu____13512 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____13512
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____13511]  in
                      FStar_Syntax_Subst.open_term uu____13510 body  in
                    match uu____13505 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13521  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____13529 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____13529  in
                            FStar_Util.Inl
                              (let uu___163_13539 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_13539.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_13539.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____13542  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_13544 = lb  in
                             let uu____13545 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_13544.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_13544.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13545;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_13544.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_13544.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13580  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_13603 = cfg  in
                             {
                               steps = (uu___165_13603.steps);
                               tcenv = (uu___165_13603.tcenv);
                               debug = (uu___165_13603.debug);
                               delta_level = (uu___165_13603.delta_level);
                               primitive_steps =
                                 (uu___165_13603.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_13603.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_13603.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13606  ->
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
               let uu____13623 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13623 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13659 =
                               let uu___166_13660 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_13660.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_13660.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13659  in
                           let uu____13661 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13661 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13687 =
                                   FStar_List.map (fun uu____13703  -> dummy)
                                     lbs1
                                    in
                                 let uu____13704 =
                                   let uu____13713 =
                                     FStar_List.map
                                       (fun uu____13733  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13713 env  in
                                 FStar_List.append uu____13687 uu____13704
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13757 =
                                       let uu___167_13758 = rc  in
                                       let uu____13759 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_13758.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13759;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_13758.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13757
                                 | uu____13766 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_13770 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_13770.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_13770.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_13770.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_13770.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13780 =
                        FStar_List.map (fun uu____13796  -> dummy) lbs2  in
                      FStar_List.append uu____13780 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13804 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13804 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_13820 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_13820.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_13820.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13847 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13847
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13866 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13942  ->
                        match uu____13942 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_14063 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_14063.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_14063.FStar_Syntax_Syntax.sort)
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
               (match uu____13866 with
                | (rec_env,memos,uu____14276) ->
                    let uu____14329 =
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
                             let uu____14640 =
                               let uu____14647 =
                                 let uu____14648 =
                                   let uu____14679 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14679, false)
                                    in
                                 Clos uu____14648  in
                               (FStar_Pervasives_Native.None, uu____14647)
                                in
                             uu____14640 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14789  ->
                     let uu____14790 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14790);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14812 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14814::uu____14815 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14820) ->
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
                             | uu____14843 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14857 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14857
                              | uu____14868 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14872 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14898 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14916 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14933 =
                        let uu____14934 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14935 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14934 uu____14935
                         in
                      failwith uu____14933
                    else rebuild cfg env stack t2
                | uu____14937 -> norm cfg env stack t2))

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
                let uu____14947 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14947  in
              let uu____14948 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14948 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14961  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____14972  ->
                        let uu____14973 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14974 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14973 uu____14974);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____14979 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____14979 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14988))::stack1 ->
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
                      | uu____15043 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15046 ->
                          let uu____15049 =
                            let uu____15050 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15050
                             in
                          failwith uu____15049
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
                  let new_steps =
                    [PureSubtermsWithinComputations;
                    Primops;
                    AllowUnboundUniverses;
                    EraseUniverses;
                    Exclude Zeta;
                    Inlining]  in
                  let uu___171_15074 = cfg  in
                  let uu____15075 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____15075;
                    tcenv = (uu___171_15074.tcenv);
                    debug = (uu___171_15074.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_15074.primitive_steps);
                    strong = (uu___171_15074.strong);
                    memoize_lazy = (uu___171_15074.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_15074.normalize_pure_lets)
                  }
                else
                  (let uu___172_15077 = cfg  in
                   {
                     steps =
                       (let uu___173_15080 = cfg.steps  in
                        {
                          beta = (uu___173_15080.beta);
                          iota = (uu___173_15080.iota);
                          zeta = false;
                          weak = (uu___173_15080.weak);
                          hnf = (uu___173_15080.hnf);
                          primops = (uu___173_15080.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_15080.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_15080.unfold_until);
                          unfold_only = (uu___173_15080.unfold_only);
                          unfold_fully = (uu___173_15080.unfold_fully);
                          unfold_attr = (uu___173_15080.unfold_attr);
                          unfold_tac = (uu___173_15080.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_15080.pure_subterms_within_computations);
                          simplify = (uu___173_15080.simplify);
                          erase_universes = (uu___173_15080.erase_universes);
                          allow_unbound_universes =
                            (uu___173_15080.allow_unbound_universes);
                          reify_ = (uu___173_15080.reify_);
                          compress_uvars = (uu___173_15080.compress_uvars);
                          no_full_norm = (uu___173_15080.no_full_norm);
                          check_no_uvars = (uu___173_15080.check_no_uvars);
                          unmeta = (uu___173_15080.unmeta);
                          unascribe = (uu___173_15080.unascribe);
                          in_full_norm_request =
                            (uu___173_15080.in_full_norm_request)
                        });
                     tcenv = (uu___172_15077.tcenv);
                     debug = (uu___172_15077.debug);
                     delta_level = (uu___172_15077.delta_level);
                     primitive_steps = (uu___172_15077.primitive_steps);
                     strong = (uu___172_15077.strong);
                     memoize_lazy = (uu___172_15077.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_15077.normalize_pure_lets)
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
                  (fun uu____15110  ->
                     let uu____15111 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____15112 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15111
                       uu____15112);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____15114 =
                   let uu____15115 = FStar_Syntax_Subst.compress head3  in
                   uu____15115.FStar_Syntax_Syntax.n  in
                 match uu____15114 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____15133 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15133
                        in
                     let uu____15134 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15134 with
                      | (uu____15135,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15141 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15149 =
                                   let uu____15150 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____15150.FStar_Syntax_Syntax.n  in
                                 match uu____15149 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15156,uu____15157))
                                     ->
                                     let uu____15166 =
                                       let uu____15167 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____15167.FStar_Syntax_Syntax.n  in
                                     (match uu____15166 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15173,msrc,uu____15175))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15184 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15184
                                      | uu____15185 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15186 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____15187 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____15187 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_15192 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_15192.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_15192.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_15192.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_15192.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_15192.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____15193 = FStar_List.tl stack  in
                                    let uu____15194 =
                                      let uu____15195 =
                                        let uu____15198 =
                                          let uu____15199 =
                                            let uu____15212 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____15212)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15199
                                           in
                                        FStar_Syntax_Syntax.mk uu____15198
                                         in
                                      uu____15195
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____15193 uu____15194
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15228 =
                                      let uu____15229 = is_return body  in
                                      match uu____15229 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15233;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15234;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15239 -> false  in
                                    if uu____15228
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
                                         let uu____15262 =
                                           let uu____15265 =
                                             let uu____15266 =
                                               let uu____15283 =
                                                 let uu____15286 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____15286]  in
                                               (uu____15283, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15266
                                              in
                                           FStar_Syntax_Syntax.mk uu____15265
                                            in
                                         uu____15262
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____15302 =
                                           let uu____15303 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____15303.FStar_Syntax_Syntax.n
                                            in
                                         match uu____15302 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15309::uu____15310::[])
                                             ->
                                             let uu____15317 =
                                               let uu____15320 =
                                                 let uu____15321 =
                                                   let uu____15328 =
                                                     let uu____15331 =
                                                       let uu____15332 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15332
                                                        in
                                                     let uu____15333 =
                                                       let uu____15336 =
                                                         let uu____15337 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15337
                                                          in
                                                       [uu____15336]  in
                                                     uu____15331 ::
                                                       uu____15333
                                                      in
                                                   (bind1, uu____15328)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15321
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15320
                                                in
                                             uu____15317
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15345 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____15351 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____15351
                                         then
                                           let uu____15354 =
                                             let uu____15355 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____15355
                                              in
                                           let uu____15356 =
                                             let uu____15359 =
                                               let uu____15360 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____15360
                                                in
                                             [uu____15359]  in
                                           uu____15354 :: uu____15356
                                         else []  in
                                       let reified =
                                         let uu____15365 =
                                           let uu____15368 =
                                             let uu____15369 =
                                               let uu____15384 =
                                                 let uu____15387 =
                                                   let uu____15390 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____15391 =
                                                     let uu____15394 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____15394]  in
                                                   uu____15390 :: uu____15391
                                                    in
                                                 let uu____15395 =
                                                   let uu____15398 =
                                                     let uu____15401 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____15402 =
                                                       let uu____15405 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____15406 =
                                                         let uu____15409 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____15410 =
                                                           let uu____15413 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____15413]  in
                                                         uu____15409 ::
                                                           uu____15410
                                                          in
                                                       uu____15405 ::
                                                         uu____15406
                                                        in
                                                     uu____15401 ::
                                                       uu____15402
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____15398
                                                    in
                                                 FStar_List.append
                                                   uu____15387 uu____15395
                                                  in
                                               (bind_inst, uu____15384)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15369
                                              in
                                           FStar_Syntax_Syntax.mk uu____15368
                                            in
                                         uu____15365
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____15425  ->
                                            let uu____15426 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____15427 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15426 uu____15427);
                                       (let uu____15428 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____15428 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____15452 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15452
                        in
                     let uu____15453 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15453 with
                      | (uu____15454,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15489 =
                                  let uu____15490 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15490.FStar_Syntax_Syntax.n  in
                                match uu____15489 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15496) -> t2
                                | uu____15501 -> head4  in
                              let uu____15502 =
                                let uu____15503 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15503.FStar_Syntax_Syntax.n  in
                              match uu____15502 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15509 -> FStar_Pervasives_Native.None
                               in
                            let uu____15510 = maybe_extract_fv head4  in
                            match uu____15510 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15520 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15520
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____15525 = maybe_extract_fv head5
                                     in
                                  match uu____15525 with
                                  | FStar_Pervasives_Native.Some uu____15530
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15531 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____15536 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15551 =
                              match uu____15551 with
                              | (e,q) ->
                                  let uu____15558 =
                                    let uu____15559 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15559.FStar_Syntax_Syntax.n  in
                                  (match uu____15558 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____15574 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____15574
                                   | uu____15575 -> false)
                               in
                            let uu____15576 =
                              let uu____15577 =
                                let uu____15584 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15584 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15577
                               in
                            if uu____15576
                            then
                              let uu____15589 =
                                let uu____15590 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15590
                                 in
                              failwith uu____15589
                            else ());
                           (let uu____15592 = maybe_unfold_action head_app
                               in
                            match uu____15592 with
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
                                   (fun uu____15633  ->
                                      let uu____15634 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15635 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15634 uu____15635);
                                 (let uu____15636 = FStar_List.tl stack  in
                                  norm cfg env uu____15636 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15638) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15662 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15662  in
                     (log cfg
                        (fun uu____15666  ->
                           let uu____15667 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15667);
                      (let uu____15668 = FStar_List.tl stack  in
                       norm cfg env uu____15668 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15789  ->
                               match uu____15789 with
                               | (pat,wopt,tm) ->
                                   let uu____15837 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15837)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15869 = FStar_List.tl stack  in
                     norm cfg env uu____15869 tm
                 | uu____15870 -> fallback ())

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
              (fun uu____15884  ->
                 let uu____15885 = FStar_Ident.string_of_lid msrc  in
                 let uu____15886 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15887 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15885
                   uu____15886 uu____15887);
            (let uu____15888 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15888
             then
               let ed =
                 let uu____15890 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15890  in
               let uu____15891 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15891 with
               | (uu____15892,return_repr) ->
                   let return_inst =
                     let uu____15901 =
                       let uu____15902 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15902.FStar_Syntax_Syntax.n  in
                     match uu____15901 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15908::[]) ->
                         let uu____15915 =
                           let uu____15918 =
                             let uu____15919 =
                               let uu____15926 =
                                 let uu____15929 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15929]  in
                               (return_tm, uu____15926)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15919  in
                           FStar_Syntax_Syntax.mk uu____15918  in
                         uu____15915 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15937 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15940 =
                     let uu____15943 =
                       let uu____15944 =
                         let uu____15959 =
                           let uu____15962 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15963 =
                             let uu____15966 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15966]  in
                           uu____15962 :: uu____15963  in
                         (return_inst, uu____15959)  in
                       FStar_Syntax_Syntax.Tm_app uu____15944  in
                     FStar_Syntax_Syntax.mk uu____15943  in
                   uu____15940 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15975 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15975 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15978 =
                      let uu____15979 = FStar_Ident.text_of_lid msrc  in
                      let uu____15980 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15979 uu____15980
                       in
                    failwith uu____15978
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15981;
                      FStar_TypeChecker_Env.mtarget = uu____15982;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15983;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15998 =
                      let uu____15999 = FStar_Ident.text_of_lid msrc  in
                      let uu____16000 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15999 uu____16000
                       in
                    failwith uu____15998
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16001;
                      FStar_TypeChecker_Env.mtarget = uu____16002;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16003;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16027 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16028 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16027 t FStar_Syntax_Syntax.tun uu____16028))

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
                (fun uu____16084  ->
                   match uu____16084 with
                   | (a,imp) ->
                       let uu____16095 = norm cfg env [] a  in
                       (uu____16095, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____16103  ->
             let uu____16104 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16105 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____16104 uu____16105);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16129 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                     uu____16129
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_16132 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_16132.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_16132.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16152 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____16152
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_16155 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_16155.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_16155.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16188  ->
                      match uu____16188 with
                      | (a,i) ->
                          let uu____16199 = norm cfg env [] a  in
                          (uu____16199, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_16217  ->
                       match uu___90_16217 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16221 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16221
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_16229 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_16232 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_16232.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_16229.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_16229.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16235  ->
        match uu____16235 with
        | (x,imp) ->
            let uu____16238 =
              let uu___179_16239 = x  in
              let uu____16240 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_16239.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_16239.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16240
              }  in
            (uu____16238, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16246 =
          FStar_List.fold_left
            (fun uu____16264  ->
               fun b  ->
                 match uu____16264 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16246 with | (nbs,uu____16304) -> FStar_List.rev nbs

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
            let uu____16320 =
              let uu___180_16321 = rc  in
              let uu____16322 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_16321.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16322;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_16321.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16320
        | uu____16329 -> lopt

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
            (let uu____16350 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16351 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____16350
               uu____16351)
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
          let uu____16371 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____16371
          then tm1
          else
            (let w t =
               let uu___181_16383 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_16383.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_16383.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16392 =
                 let uu____16393 = FStar_Syntax_Util.unmeta t  in
                 uu____16393.FStar_Syntax_Syntax.n  in
               match uu____16392 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16400 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16445)::args1,(bv,uu____16448)::bs1) ->
                   let uu____16482 =
                     let uu____16483 = FStar_Syntax_Subst.compress t  in
                     uu____16483.FStar_Syntax_Syntax.n  in
                   (match uu____16482 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16487 -> false)
               | ([],[]) -> true
               | (uu____16508,uu____16509) -> false  in
             let is_applied bs t =
               let uu____16545 = FStar_Syntax_Util.head_and_args' t  in
               match uu____16545 with
               | (hd1,args) ->
                   let uu____16578 =
                     let uu____16579 = FStar_Syntax_Subst.compress hd1  in
                     uu____16579.FStar_Syntax_Syntax.n  in
                   (match uu____16578 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____16585 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____16597 = FStar_Syntax_Util.is_squash t  in
               match uu____16597 with
               | FStar_Pervasives_Native.Some (uu____16608,t') ->
                   is_applied bs t'
               | uu____16620 ->
                   let uu____16629 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____16629 with
                    | FStar_Pervasives_Native.Some (uu____16640,t') ->
                        is_applied bs t'
                    | uu____16652 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____16669 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16669 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16676)::(q,uu____16678)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____16713 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____16713 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____16718 =
                          let uu____16719 = FStar_Syntax_Subst.compress p  in
                          uu____16719.FStar_Syntax_Syntax.n  in
                        (match uu____16718 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16725 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____16725
                         | uu____16726 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____16729)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____16754 =
                          let uu____16755 = FStar_Syntax_Subst.compress p1
                             in
                          uu____16755.FStar_Syntax_Syntax.n  in
                        (match uu____16754 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16761 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____16761
                         | uu____16762 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____16766 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____16766 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____16771 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____16771 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16778 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16778
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____16781)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16806 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____16806 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16813 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16813
                              | uu____16814 -> FStar_Pervasives_Native.None)
                         | uu____16817 -> FStar_Pervasives_Native.None)
                    | uu____16820 -> FStar_Pervasives_Native.None)
               | uu____16823 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16834 =
                 let uu____16835 = FStar_Syntax_Subst.compress phi  in
                 uu____16835.FStar_Syntax_Syntax.n  in
               match uu____16834 with
               | FStar_Syntax_Syntax.Tm_match (uu____16840,br::brs) ->
                   let uu____16907 = br  in
                   (match uu____16907 with
                    | (uu____16924,uu____16925,e) ->
                        let r =
                          let uu____16946 = simp_t e  in
                          match uu____16946 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16952 =
                                FStar_List.for_all
                                  (fun uu____16970  ->
                                     match uu____16970 with
                                     | (uu____16983,uu____16984,e') ->
                                         let uu____16998 = simp_t e'  in
                                         uu____16998 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16952
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17006 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17011 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17011
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17032 =
                 match uu____17032 with
                 | (t1,q) ->
                     let uu____17045 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17045 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17073 -> (t1, q))
                  in
               let uu____17082 = FStar_Syntax_Util.head_and_args t  in
               match uu____17082 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____17144 =
                 let uu____17145 = FStar_Syntax_Util.unmeta ty  in
                 uu____17145.FStar_Syntax_Syntax.n  in
               match uu____17144 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17149) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17154,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17174 -> false  in
             let simplify1 arg =
               let uu____17197 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17197, arg)  in
             let uu____17206 = is_quantified_const tm1  in
             match uu____17206 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____17210 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____17210
             | FStar_Pervasives_Native.None  ->
                 let uu____17211 =
                   let uu____17212 = FStar_Syntax_Subst.compress tm1  in
                   uu____17212.FStar_Syntax_Syntax.n  in
                 (match uu____17211 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17216;
                              FStar_Syntax_Syntax.vars = uu____17217;_},uu____17218);
                         FStar_Syntax_Syntax.pos = uu____17219;
                         FStar_Syntax_Syntax.vars = uu____17220;_},args)
                      ->
                      let uu____17246 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17246
                      then
                        let uu____17247 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17247 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17294)::
                             (uu____17295,(arg,uu____17297))::[] ->
                             maybe_auto_squash arg
                         | (uu____17346,(arg,uu____17348))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17349)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17398)::uu____17399::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17450::(FStar_Pervasives_Native.Some (false
                                         ),uu____17451)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17502 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17516 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17516
                         then
                           let uu____17517 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17517 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17564)::uu____17565::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17616::(FStar_Pervasives_Native.Some (true
                                           ),uu____17617)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17668)::(uu____17669,(arg,uu____17671))::[]
                               -> maybe_auto_squash arg
                           | (uu____17720,(arg,uu____17722))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17723)::[]
                               -> maybe_auto_squash arg
                           | uu____17772 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17786 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17786
                            then
                              let uu____17787 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17787 with
                              | uu____17834::(FStar_Pervasives_Native.Some
                                              (true ),uu____17835)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17886)::uu____17887::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17938)::(uu____17939,(arg,uu____17941))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17990,(p,uu____17992))::(uu____17993,
                                                                (q,uu____17995))::[]
                                  ->
                                  let uu____18042 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18042
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18044 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18058 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18058
                               then
                                 let uu____18059 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18059 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18106)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18107)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18158)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18159)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18210)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18211)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18262)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18263)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18314,(arg,uu____18316))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18317)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18366)::(uu____18367,(arg,uu____18369))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18418,(arg,uu____18420))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18421)::[]
                                     ->
                                     let uu____18470 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18470
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18471)::(uu____18472,(arg,uu____18474))::[]
                                     ->
                                     let uu____18523 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18523
                                 | (uu____18524,(p,uu____18526))::(uu____18527,
                                                                   (q,uu____18529))::[]
                                     ->
                                     let uu____18576 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18576
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18578 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18592 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18592
                                  then
                                    let uu____18593 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18593 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18640)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18671)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18702 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18716 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18716
                                     then
                                       match args with
                                       | (t,uu____18718)::[] ->
                                           let uu____18735 =
                                             let uu____18736 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18736.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18735 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18739::[],body,uu____18741)
                                                ->
                                                let uu____18768 = simp_t body
                                                   in
                                                (match uu____18768 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18771 -> tm1)
                                            | uu____18774 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18776))::(t,uu____18778)::[]
                                           ->
                                           let uu____18817 =
                                             let uu____18818 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18818.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18817 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18821::[],body,uu____18823)
                                                ->
                                                let uu____18850 = simp_t body
                                                   in
                                                (match uu____18850 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18853 -> tm1)
                                            | uu____18856 -> tm1)
                                       | uu____18857 -> tm1
                                     else
                                       (let uu____18867 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18867
                                        then
                                          match args with
                                          | (t,uu____18869)::[] ->
                                              let uu____18886 =
                                                let uu____18887 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18887.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18886 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18890::[],body,uu____18892)
                                                   ->
                                                   let uu____18919 =
                                                     simp_t body  in
                                                   (match uu____18919 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18922 -> tm1)
                                               | uu____18925 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18927))::(t,uu____18929)::[]
                                              ->
                                              let uu____18968 =
                                                let uu____18969 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18969.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18968 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18972::[],body,uu____18974)
                                                   ->
                                                   let uu____19001 =
                                                     simp_t body  in
                                                   (match uu____19001 with
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
                                                    | uu____19004 -> tm1)
                                               | uu____19007 -> tm1)
                                          | uu____19008 -> tm1
                                        else
                                          (let uu____19018 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19018
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19019;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19020;_},uu____19021)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19038;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19039;_},uu____19040)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19057 -> tm1
                                           else
                                             (let uu____19067 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19067 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19087 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____19097;
                         FStar_Syntax_Syntax.vars = uu____19098;_},args)
                      ->
                      let uu____19120 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19120
                      then
                        let uu____19121 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19121 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19168)::
                             (uu____19169,(arg,uu____19171))::[] ->
                             maybe_auto_squash arg
                         | (uu____19220,(arg,uu____19222))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19223)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19272)::uu____19273::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19324::(FStar_Pervasives_Native.Some (false
                                         ),uu____19325)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19376 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19390 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19390
                         then
                           let uu____19391 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19391 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19438)::uu____19439::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19490::(FStar_Pervasives_Native.Some (true
                                           ),uu____19491)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19542)::(uu____19543,(arg,uu____19545))::[]
                               -> maybe_auto_squash arg
                           | (uu____19594,(arg,uu____19596))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19597)::[]
                               -> maybe_auto_squash arg
                           | uu____19646 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19660 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19660
                            then
                              let uu____19661 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19661 with
                              | uu____19708::(FStar_Pervasives_Native.Some
                                              (true ),uu____19709)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19760)::uu____19761::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19812)::(uu____19813,(arg,uu____19815))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19864,(p,uu____19866))::(uu____19867,
                                                                (q,uu____19869))::[]
                                  ->
                                  let uu____19916 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19916
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19918 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19932 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19932
                               then
                                 let uu____19933 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19933 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19980)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19981)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20032)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20033)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20084)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20085)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20136)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20137)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20188,(arg,uu____20190))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20191)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20240)::(uu____20241,(arg,uu____20243))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20292,(arg,uu____20294))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20295)::[]
                                     ->
                                     let uu____20344 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20344
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20345)::(uu____20346,(arg,uu____20348))::[]
                                     ->
                                     let uu____20397 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20397
                                 | (uu____20398,(p,uu____20400))::(uu____20401,
                                                                   (q,uu____20403))::[]
                                     ->
                                     let uu____20450 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20450
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20452 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20466 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20466
                                  then
                                    let uu____20467 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20467 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20514)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20545)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20576 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20590 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20590
                                     then
                                       match args with
                                       | (t,uu____20592)::[] ->
                                           let uu____20609 =
                                             let uu____20610 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20610.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20609 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20613::[],body,uu____20615)
                                                ->
                                                let uu____20642 = simp_t body
                                                   in
                                                (match uu____20642 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20645 -> tm1)
                                            | uu____20648 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20650))::(t,uu____20652)::[]
                                           ->
                                           let uu____20691 =
                                             let uu____20692 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20692.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20691 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20695::[],body,uu____20697)
                                                ->
                                                let uu____20724 = simp_t body
                                                   in
                                                (match uu____20724 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20727 -> tm1)
                                            | uu____20730 -> tm1)
                                       | uu____20731 -> tm1
                                     else
                                       (let uu____20741 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20741
                                        then
                                          match args with
                                          | (t,uu____20743)::[] ->
                                              let uu____20760 =
                                                let uu____20761 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20761.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20760 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20764::[],body,uu____20766)
                                                   ->
                                                   let uu____20793 =
                                                     simp_t body  in
                                                   (match uu____20793 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20796 -> tm1)
                                               | uu____20799 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20801))::(t,uu____20803)::[]
                                              ->
                                              let uu____20842 =
                                                let uu____20843 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20843.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20842 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20846::[],body,uu____20848)
                                                   ->
                                                   let uu____20875 =
                                                     simp_t body  in
                                                   (match uu____20875 with
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
                                                    | uu____20878 -> tm1)
                                               | uu____20881 -> tm1)
                                          | uu____20882 -> tm1
                                        else
                                          (let uu____20892 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20892
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20893;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20894;_},uu____20895)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20912;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20913;_},uu____20914)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20931 -> tm1
                                           else
                                             (let uu____20941 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20941 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20961 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20976 = simp_t t  in
                      (match uu____20976 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20979 ->
                      let uu____21002 = is_const_match tm1  in
                      (match uu____21002 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____21005 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____21015  ->
               (let uu____21017 = FStar_Syntax_Print.tag_of_term t  in
                let uu____21018 = FStar_Syntax_Print.term_to_string t  in
                let uu____21019 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____21026 =
                  let uu____21027 =
                    let uu____21030 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____21030
                     in
                  stack_to_string uu____21027  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____21017 uu____21018 uu____21019 uu____21026);
               (let uu____21053 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____21053
                then
                  let uu____21054 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____21054 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____21061 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____21062 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____21063 =
                          let uu____21064 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____21064
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____21061
                          uu____21062 uu____21063);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____21082 =
                     let uu____21083 =
                       let uu____21084 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____21084  in
                     FStar_Util.string_of_int uu____21083  in
                   let uu____21089 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____21090 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____21082 uu____21089 uu____21090)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____21096,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____21145  ->
                     let uu____21146 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____21146);
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
               let uu____21182 =
                 let uu___182_21183 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_21183.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_21183.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____21182
           | (Arg (Univ uu____21184,uu____21185,uu____21186))::uu____21187 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____21190,uu____21191))::uu____21192 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____21207,uu____21208),aq,r))::stack1
               when
               let uu____21258 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____21258 ->
               let t2 =
                 let uu____21262 =
                   let uu____21263 =
                     let uu____21264 = closure_as_term cfg env_arg tm  in
                     (uu____21264, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____21263  in
                 uu____21262 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____21270),aq,r))::stack1 ->
               (log cfg
                  (fun uu____21323  ->
                     let uu____21324 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____21324);
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
                  (let uu____21334 = FStar_ST.op_Bang m  in
                   match uu____21334 with
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
                   | FStar_Pervasives_Native.Some (uu____21471,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21518 =
                 log cfg
                   (fun uu____21522  ->
                      let uu____21523 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21523);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21527 =
                 let uu____21528 = FStar_Syntax_Subst.compress t1  in
                 uu____21528.FStar_Syntax_Syntax.n  in
               (match uu____21527 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21555 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21555  in
                    (log cfg
                       (fun uu____21559  ->
                          let uu____21560 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21560);
                     (let uu____21561 = FStar_List.tl stack  in
                      norm cfg env1 uu____21561 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21562);
                       FStar_Syntax_Syntax.pos = uu____21563;
                       FStar_Syntax_Syntax.vars = uu____21564;_},(e,uu____21566)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21595 when
                    (cfg.steps).primops ->
                    let uu____21610 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21610 with
                     | (hd1,args) ->
                         let uu____21647 =
                           let uu____21648 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21648.FStar_Syntax_Syntax.n  in
                         (match uu____21647 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21652 = find_prim_step cfg fv  in
                              (match uu____21652 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21655; arity = uu____21656;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21658;
                                     requires_binder_substitution =
                                       uu____21659;
                                     interpretation = uu____21660;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21673 -> fallback " (3)" ())
                          | uu____21676 -> fallback " (4)" ()))
                | uu____21677 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____21698  ->
                     let uu____21699 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21699);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21706 =
                   log cfg1
                     (fun uu____21711  ->
                        let uu____21712 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21713 =
                          let uu____21714 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21731  ->
                                    match uu____21731 with
                                    | (p,uu____21741,uu____21742) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21714
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21712 uu____21713);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_21759  ->
                                match uu___91_21759 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21760 -> false))
                         in
                      let steps =
                        let uu___183_21762 = cfg1.steps  in
                        {
                          beta = (uu___183_21762.beta);
                          iota = (uu___183_21762.iota);
                          zeta = false;
                          weak = (uu___183_21762.weak);
                          hnf = (uu___183_21762.hnf);
                          primops = (uu___183_21762.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_21762.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_21762.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_21762.pure_subterms_within_computations);
                          simplify = (uu___183_21762.simplify);
                          erase_universes = (uu___183_21762.erase_universes);
                          allow_unbound_universes =
                            (uu___183_21762.allow_unbound_universes);
                          reify_ = (uu___183_21762.reify_);
                          compress_uvars = (uu___183_21762.compress_uvars);
                          no_full_norm = (uu___183_21762.no_full_norm);
                          check_no_uvars = (uu___183_21762.check_no_uvars);
                          unmeta = (uu___183_21762.unmeta);
                          unascribe = (uu___183_21762.unascribe);
                          in_full_norm_request =
                            (uu___183_21762.in_full_norm_request)
                        }  in
                      let uu___184_21767 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_21767.tcenv);
                        debug = (uu___184_21767.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_21767.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_21767.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_21767.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21799 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21820 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21880  ->
                                    fun uu____21881  ->
                                      match (uu____21880, uu____21881) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21972 = norm_pat env3 p1
                                             in
                                          (match uu____21972 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21820 with
                           | (pats1,env3) ->
                               ((let uu___185_22054 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_22054.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_22073 = x  in
                            let uu____22074 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_22073.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_22073.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22074
                            }  in
                          ((let uu___187_22088 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_22088.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_22099 = x  in
                            let uu____22100 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_22099.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_22099.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22100
                            }  in
                          ((let uu___189_22114 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_22114.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_22130 = x  in
                            let uu____22131 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_22130.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_22130.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22131
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_22138 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_22138.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____22148 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____22162 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____22162 with
                                  | (p,wopt,e) ->
                                      let uu____22182 = norm_pat env1 p  in
                                      (match uu____22182 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22207 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22207
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22214 =
                        (((cfg1.steps).iota &&
                            (Prims.op_Negation (cfg1.steps).weak))
                           && (Prims.op_Negation (cfg1.steps).compress_uvars))
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____22214
                      then norm cfg1 scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22216 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22216)
                    in
                 let rec is_cons head1 =
                   let uu____22221 =
                     let uu____22222 = FStar_Syntax_Subst.compress head1  in
                     uu____22222.FStar_Syntax_Syntax.n  in
                   match uu____22221 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22226) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22231 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22232;
                         FStar_Syntax_Syntax.fv_delta = uu____22233;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22234;
                         FStar_Syntax_Syntax.fv_delta = uu____22235;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22236);_}
                       -> true
                   | uu____22243 -> false  in
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
                   let uu____22388 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____22388 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22475 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22514 ->
                                 let uu____22515 =
                                   let uu____22516 = is_cons head1  in
                                   Prims.op_Negation uu____22516  in
                                 FStar_Util.Inr uu____22515)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22541 =
                              let uu____22542 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22542.FStar_Syntax_Syntax.n  in
                            (match uu____22541 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22560 ->
                                 let uu____22561 =
                                   let uu____22562 = is_cons head1  in
                                   Prims.op_Negation uu____22562  in
                                 FStar_Util.Inr uu____22561))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22631)::rest_a,(p1,uu____22634)::rest_p) ->
                       let uu____22678 = matches_pat t2 p1  in
                       (match uu____22678 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22727 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22833 = matches_pat scrutinee1 p1  in
                       (match uu____22833 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____22873  ->
                                  let uu____22874 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22875 =
                                    let uu____22876 =
                                      FStar_List.map
                                        (fun uu____22886  ->
                                           match uu____22886 with
                                           | (uu____22891,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22876
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22874 uu____22875);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22923  ->
                                       match uu____22923 with
                                       | (bv,t2) ->
                                           let uu____22946 =
                                             let uu____22953 =
                                               let uu____22956 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22956
                                                in
                                             let uu____22957 =
                                               let uu____22958 =
                                                 let uu____22989 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22989, false)
                                                  in
                                               Clos uu____22958  in
                                             (uu____22953, uu____22957)  in
                                           uu____22946 :: env2) env1 s
                                 in
                              let uu____23106 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23106)))
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
    let uu____23129 =
      let uu____23132 = FStar_ST.op_Bang plugins  in p :: uu____23132  in
    FStar_ST.op_Colon_Equals plugins uu____23129  in
  let retrieve uu____23230 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____23295  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_23328  ->
                  match uu___92_23328 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____23332 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____23338 -> d  in
        let uu____23341 = to_fsteps s  in
        let uu____23342 =
          let uu____23343 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____23344 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____23345 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____23346 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____23347 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____23343;
            primop = uu____23344;
            b380 = uu____23345;
            norm_delayed = uu____23346;
            print_normalized = uu____23347
          }  in
        let uu____23348 =
          let uu____23351 =
            let uu____23354 = retrieve_plugins ()  in
            FStar_List.append uu____23354 psteps  in
          add_steps built_in_primitive_steps uu____23351  in
        let uu____23357 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____23359 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____23359)
           in
        {
          steps = uu____23341;
          tcenv = e;
          debug = uu____23342;
          delta_level = d1;
          primitive_steps = uu____23348;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____23357
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
      fun t  -> let uu____23417 = config s e  in norm_comp uu____23417 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23430 = config [] env  in norm_universe uu____23430 [] u
  
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
        let uu____23448 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23448  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23455 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___192_23474 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___192_23474.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___192_23474.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23481 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23481
          then
            let ct1 =
              let uu____23483 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23483 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23490 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23490
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___193_23494 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___193_23494.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___193_23494.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___193_23494.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___194_23496 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___194_23496.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___194_23496.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___194_23496.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___194_23496.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___195_23497 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___195_23497.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_23497.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23499 -> c
  
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
        let uu____23511 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23511  in
      let uu____23518 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23518
      then
        let uu____23519 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23519 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23525  ->
                 let uu____23526 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23526)
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
            ((let uu____23543 =
                let uu____23548 =
                  let uu____23549 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23549
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23548)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23543);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23560 = config [AllowUnboundUniverses] env  in
          norm_comp uu____23560 [] c
        with
        | e ->
            ((let uu____23573 =
                let uu____23578 =
                  let uu____23579 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23579
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23578)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23573);
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
                   let uu____23616 =
                     let uu____23617 =
                       let uu____23624 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____23624)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23617  in
                   mk uu____23616 t01.FStar_Syntax_Syntax.pos
               | uu____23629 -> t2)
          | uu____23630 -> t2  in
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
        let uu____23670 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23670 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23699 ->
                 let uu____23706 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23706 with
                  | (actuals,uu____23716,uu____23717) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23731 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23731 with
                         | (binders,args) ->
                             let uu____23748 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23748
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
      | uu____23756 ->
          let uu____23757 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23757 with
           | (head1,args) ->
               let uu____23794 =
                 let uu____23795 = FStar_Syntax_Subst.compress head1  in
                 uu____23795.FStar_Syntax_Syntax.n  in
               (match uu____23794 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23798,thead) ->
                    let uu____23824 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23824 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23866 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_23874 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_23874.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_23874.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_23874.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_23874.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_23874.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_23874.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_23874.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_23874.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_23874.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_23874.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_23874.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_23874.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_23874.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_23874.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_23874.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_23874.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_23874.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_23874.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___200_23874.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___200_23874.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___200_23874.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_23874.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_23874.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___200_23874.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___200_23874.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___200_23874.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___200_23874.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___200_23874.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___200_23874.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___200_23874.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___200_23874.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___200_23874.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___200_23874.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___200_23874.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23866 with
                            | (uu____23875,ty,uu____23877) ->
                                eta_expand_with_type env t ty))
                | uu____23878 ->
                    let uu____23879 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_23887 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_23887.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_23887.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_23887.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_23887.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_23887.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_23887.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_23887.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_23887.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_23887.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_23887.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_23887.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_23887.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_23887.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_23887.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_23887.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_23887.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_23887.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_23887.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___201_23887.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___201_23887.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___201_23887.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_23887.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_23887.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___201_23887.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___201_23887.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___201_23887.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___201_23887.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___201_23887.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___201_23887.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___201_23887.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___201_23887.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___201_23887.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___201_23887.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___201_23887.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23879 with
                     | (uu____23888,ty,uu____23890) ->
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
      let uu___202_23947 = x  in
      let uu____23948 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___202_23947.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___202_23947.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23948
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23951 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23976 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23977 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23978 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23979 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23986 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23987 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23988 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___203_24016 = rc  in
          let uu____24017 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____24024 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___203_24016.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____24017;
            FStar_Syntax_Syntax.residual_flags = uu____24024
          }  in
        let uu____24027 =
          let uu____24028 =
            let uu____24045 = elim_delayed_subst_binders bs  in
            let uu____24052 = elim_delayed_subst_term t2  in
            let uu____24053 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____24045, uu____24052, uu____24053)  in
          FStar_Syntax_Syntax.Tm_abs uu____24028  in
        mk1 uu____24027
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____24082 =
          let uu____24083 =
            let uu____24096 = elim_delayed_subst_binders bs  in
            let uu____24103 = elim_delayed_subst_comp c  in
            (uu____24096, uu____24103)  in
          FStar_Syntax_Syntax.Tm_arrow uu____24083  in
        mk1 uu____24082
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24116 =
          let uu____24117 =
            let uu____24124 = elim_bv bv  in
            let uu____24125 = elim_delayed_subst_term phi  in
            (uu____24124, uu____24125)  in
          FStar_Syntax_Syntax.Tm_refine uu____24117  in
        mk1 uu____24116
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24148 =
          let uu____24149 =
            let uu____24164 = elim_delayed_subst_term t2  in
            let uu____24165 = elim_delayed_subst_args args  in
            (uu____24164, uu____24165)  in
          FStar_Syntax_Syntax.Tm_app uu____24149  in
        mk1 uu____24148
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___204_24229 = p  in
              let uu____24230 =
                let uu____24231 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24231  in
              {
                FStar_Syntax_Syntax.v = uu____24230;
                FStar_Syntax_Syntax.p =
                  (uu___204_24229.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___205_24233 = p  in
              let uu____24234 =
                let uu____24235 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24235  in
              {
                FStar_Syntax_Syntax.v = uu____24234;
                FStar_Syntax_Syntax.p =
                  (uu___205_24233.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___206_24242 = p  in
              let uu____24243 =
                let uu____24244 =
                  let uu____24251 = elim_bv x  in
                  let uu____24252 = elim_delayed_subst_term t0  in
                  (uu____24251, uu____24252)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24244  in
              {
                FStar_Syntax_Syntax.v = uu____24243;
                FStar_Syntax_Syntax.p =
                  (uu___206_24242.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___207_24271 = p  in
              let uu____24272 =
                let uu____24273 =
                  let uu____24286 =
                    FStar_List.map
                      (fun uu____24309  ->
                         match uu____24309 with
                         | (x,b) ->
                             let uu____24322 = elim_pat x  in
                             (uu____24322, b)) pats
                     in
                  (fv, uu____24286)  in
                FStar_Syntax_Syntax.Pat_cons uu____24273  in
              {
                FStar_Syntax_Syntax.v = uu____24272;
                FStar_Syntax_Syntax.p =
                  (uu___207_24271.FStar_Syntax_Syntax.p)
              }
          | uu____24335 -> p  in
        let elim_branch uu____24357 =
          match uu____24357 with
          | (pat,wopt,t3) ->
              let uu____24383 = elim_pat pat  in
              let uu____24386 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24389 = elim_delayed_subst_term t3  in
              (uu____24383, uu____24386, uu____24389)
           in
        let uu____24394 =
          let uu____24395 =
            let uu____24418 = elim_delayed_subst_term t2  in
            let uu____24419 = FStar_List.map elim_branch branches  in
            (uu____24418, uu____24419)  in
          FStar_Syntax_Syntax.Tm_match uu____24395  in
        mk1 uu____24394
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24528 =
          match uu____24528 with
          | (tc,topt) ->
              let uu____24563 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24573 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24573
                | FStar_Util.Inr c ->
                    let uu____24575 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24575
                 in
              let uu____24576 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24563, uu____24576)
           in
        let uu____24585 =
          let uu____24586 =
            let uu____24613 = elim_delayed_subst_term t2  in
            let uu____24614 = elim_ascription a  in
            (uu____24613, uu____24614, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24586  in
        mk1 uu____24585
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___208_24659 = lb  in
          let uu____24660 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24663 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___208_24659.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___208_24659.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24660;
            FStar_Syntax_Syntax.lbeff =
              (uu___208_24659.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24663;
            FStar_Syntax_Syntax.lbattrs =
              (uu___208_24659.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___208_24659.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24666 =
          let uu____24667 =
            let uu____24680 =
              let uu____24687 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24687)  in
            let uu____24696 = elim_delayed_subst_term t2  in
            (uu____24680, uu____24696)  in
          FStar_Syntax_Syntax.Tm_let uu____24667  in
        mk1 uu____24666
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24729 =
          let uu____24730 =
            let uu____24747 = elim_delayed_subst_term t2  in
            (uv, uu____24747)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24730  in
        mk1 uu____24729
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24765 =
          let uu____24766 =
            let uu____24773 = elim_delayed_subst_term tm  in
            (uu____24773, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24766  in
        mk1 uu____24765
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24780 =
          let uu____24781 =
            let uu____24788 = elim_delayed_subst_term t2  in
            let uu____24789 = elim_delayed_subst_meta md  in
            (uu____24788, uu____24789)  in
          FStar_Syntax_Syntax.Tm_meta uu____24781  in
        mk1 uu____24780

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24796  ->
         match uu___93_24796 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24800 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24800
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
        let uu____24821 =
          let uu____24822 =
            let uu____24831 = elim_delayed_subst_term t  in
            (uu____24831, uopt)  in
          FStar_Syntax_Syntax.Total uu____24822  in
        mk1 uu____24821
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24844 =
          let uu____24845 =
            let uu____24854 = elim_delayed_subst_term t  in
            (uu____24854, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24845  in
        mk1 uu____24844
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___209_24859 = ct  in
          let uu____24860 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24863 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24872 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___209_24859.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___209_24859.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24860;
            FStar_Syntax_Syntax.effect_args = uu____24863;
            FStar_Syntax_Syntax.flags = uu____24872
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24875  ->
    match uu___94_24875 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24887 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24887
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24920 =
          let uu____24927 = elim_delayed_subst_term t  in (m, uu____24927)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24920
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24935 =
          let uu____24944 = elim_delayed_subst_term t  in
          (m1, m2, uu____24944)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24935
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24967  ->
         match uu____24967 with
         | (t,q) ->
             let uu____24978 = elim_delayed_subst_term t  in (uu____24978, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24998  ->
         match uu____24998 with
         | (x,q) ->
             let uu____25009 =
               let uu___210_25010 = x  in
               let uu____25011 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___210_25010.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___210_25010.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____25011
               }  in
             (uu____25009, q)) bs

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
            | (uu____25087,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25093,FStar_Util.Inl t) ->
                let uu____25099 =
                  let uu____25102 =
                    let uu____25103 =
                      let uu____25116 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25116)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25103  in
                  FStar_Syntax_Syntax.mk uu____25102  in
                uu____25099 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25120 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25120 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25148 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25203 ->
                    let uu____25204 =
                      let uu____25213 =
                        let uu____25214 = FStar_Syntax_Subst.compress t4  in
                        uu____25214.FStar_Syntax_Syntax.n  in
                      (uu____25213, tc)  in
                    (match uu____25204 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25239) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25276) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25315,FStar_Util.Inl uu____25316) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25339 -> failwith "Impossible")
                 in
              (match uu____25148 with
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
          let uu____25444 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25444 with
          | (univ_names1,binders1,tc) ->
              let uu____25502 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25502)
  
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
          let uu____25537 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25537 with
          | (univ_names1,binders1,tc) ->
              let uu____25597 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25597)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25630 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25630 with
           | (univ_names1,binders1,typ1) ->
               let uu___211_25658 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_25658.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_25658.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_25658.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_25658.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___212_25679 = s  in
          let uu____25680 =
            let uu____25681 =
              let uu____25690 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25690, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25681  in
          {
            FStar_Syntax_Syntax.sigel = uu____25680;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_25679.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_25679.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_25679.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_25679.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25707 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25707 with
           | (univ_names1,uu____25725,typ1) ->
               let uu___213_25739 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_25739.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_25739.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_25739.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_25739.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25745 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25745 with
           | (univ_names1,uu____25763,typ1) ->
               let uu___214_25777 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_25777.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_25777.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_25777.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_25777.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25811 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25811 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25834 =
                            let uu____25835 =
                              let uu____25836 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25836  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25835
                             in
                          elim_delayed_subst_term uu____25834  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___215_25839 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___215_25839.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_25839.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___215_25839.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___215_25839.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___216_25840 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___216_25840.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_25840.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_25840.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_25840.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___217_25852 = s  in
          let uu____25853 =
            let uu____25854 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25854  in
          {
            FStar_Syntax_Syntax.sigel = uu____25853;
            FStar_Syntax_Syntax.sigrng =
              (uu___217_25852.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_25852.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_25852.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_25852.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25858 = elim_uvars_aux_t env us [] t  in
          (match uu____25858 with
           | (us1,uu____25876,t1) ->
               let uu___218_25890 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_25890.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_25890.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_25890.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_25890.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25891 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25893 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25893 with
           | (univs1,binders,signature) ->
               let uu____25921 =
                 let uu____25930 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____25930 with
                 | (univs_opening,univs2) ->
                     let uu____25957 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25957)
                  in
               (match uu____25921 with
                | (univs_opening,univs_closing) ->
                    let uu____25974 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25980 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25981 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25980, uu____25981)  in
                    (match uu____25974 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26003 =
                           match uu____26003 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26021 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26021 with
                                | (us1,t1) ->
                                    let uu____26032 =
                                      let uu____26037 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26044 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26037, uu____26044)  in
                                    (match uu____26032 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26057 =
                                           let uu____26062 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26071 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26062, uu____26071)  in
                                         (match uu____26057 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26087 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26087
                                                 in
                                              let uu____26088 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26088 with
                                               | (uu____26109,uu____26110,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26125 =
                                                       let uu____26126 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26126
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26125
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26131 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26131 with
                           | (uu____26144,uu____26145,t1) -> t1  in
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
                             | uu____26205 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26222 =
                               let uu____26223 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26223.FStar_Syntax_Syntax.n  in
                             match uu____26222 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26282 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26311 =
                               let uu____26312 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26312.FStar_Syntax_Syntax.n  in
                             match uu____26311 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26333) ->
                                 let uu____26354 = destruct_action_body body
                                    in
                                 (match uu____26354 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26399 ->
                                 let uu____26400 = destruct_action_body t  in
                                 (match uu____26400 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26449 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26449 with
                           | (action_univs,t) ->
                               let uu____26458 = destruct_action_typ_templ t
                                  in
                               (match uu____26458 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___219_26499 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___219_26499.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___219_26499.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___220_26501 = ed  in
                           let uu____26502 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26503 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26504 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26505 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26506 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26507 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26508 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26509 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26510 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26511 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26512 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26513 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26514 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26515 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___220_26501.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___220_26501.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26502;
                             FStar_Syntax_Syntax.bind_wp = uu____26503;
                             FStar_Syntax_Syntax.if_then_else = uu____26504;
                             FStar_Syntax_Syntax.ite_wp = uu____26505;
                             FStar_Syntax_Syntax.stronger = uu____26506;
                             FStar_Syntax_Syntax.close_wp = uu____26507;
                             FStar_Syntax_Syntax.assert_p = uu____26508;
                             FStar_Syntax_Syntax.assume_p = uu____26509;
                             FStar_Syntax_Syntax.null_wp = uu____26510;
                             FStar_Syntax_Syntax.trivial = uu____26511;
                             FStar_Syntax_Syntax.repr = uu____26512;
                             FStar_Syntax_Syntax.return_repr = uu____26513;
                             FStar_Syntax_Syntax.bind_repr = uu____26514;
                             FStar_Syntax_Syntax.actions = uu____26515;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___220_26501.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___221_26518 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___221_26518.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___221_26518.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___221_26518.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___221_26518.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_26535 =
            match uu___95_26535 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26562 = elim_uvars_aux_t env us [] t  in
                (match uu____26562 with
                 | (us1,uu____26586,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___222_26605 = sub_eff  in
            let uu____26606 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26609 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___222_26605.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___222_26605.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26606;
              FStar_Syntax_Syntax.lift = uu____26609
            }  in
          let uu___223_26612 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___223_26612.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_26612.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_26612.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_26612.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26622 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26622 with
           | (univ_names1,binders1,comp1) ->
               let uu___224_26656 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_26656.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_26656.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_26656.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_26656.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26667 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26668 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  