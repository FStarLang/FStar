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
               let uu____10282 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____10282
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10312 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10312)
               ->
               let cfg' =
                 let uu___147_10314 = cfg  in
                 {
                   steps =
                     (let uu___148_10317 = cfg.steps  in
                      {
                        beta = (uu___148_10317.beta);
                        iota = (uu___148_10317.iota);
                        zeta = (uu___148_10317.zeta);
                        weak = (uu___148_10317.weak);
                        hnf = (uu___148_10317.hnf);
                        primops = (uu___148_10317.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_10317.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_10317.unfold_attr);
                        unfold_tac = (uu___148_10317.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_10317.pure_subterms_within_computations);
                        simplify = (uu___148_10317.simplify);
                        erase_universes = (uu___148_10317.erase_universes);
                        allow_unbound_universes =
                          (uu___148_10317.allow_unbound_universes);
                        reify_ = (uu___148_10317.reify_);
                        compress_uvars = (uu___148_10317.compress_uvars);
                        no_full_norm = (uu___148_10317.no_full_norm);
                        check_no_uvars = (uu___148_10317.check_no_uvars);
                        unmeta = (uu___148_10317.unmeta);
                        unascribe = (uu___148_10317.unascribe);
                        in_full_norm_request =
                          (uu___148_10317.in_full_norm_request)
                      });
                   tcenv = (uu___147_10314.tcenv);
                   debug = (uu___147_10314.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_10314.primitive_steps);
                   strong = (uu___147_10314.strong);
                   memoize_lazy = (uu___147_10314.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10322 = get_norm_request (norm cfg' env []) args  in
               (match uu____10322 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10353  ->
                              fun stack1  ->
                                match uu____10353 with
                                | (a,aq) ->
                                    let uu____10365 =
                                      let uu____10366 =
                                        let uu____10373 =
                                          let uu____10374 =
                                            let uu____10405 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10405, false)  in
                                          Clos uu____10374  in
                                        (uu____10373, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10366  in
                                    uu____10365 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10489  ->
                          let uu____10490 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10490);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10512 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10517  ->
                                match uu___88_10517 with
                                | UnfoldUntil uu____10518 -> true
                                | UnfoldOnly uu____10519 -> true
                                | UnfoldFully uu____10522 -> true
                                | uu____10525 -> false))
                         in
                      if uu____10512
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_10530 = cfg  in
                      let uu____10531 =
                        let uu___150_10532 = to_fsteps s  in
                        {
                          beta = (uu___150_10532.beta);
                          iota = (uu___150_10532.iota);
                          zeta = (uu___150_10532.zeta);
                          weak = (uu___150_10532.weak);
                          hnf = (uu___150_10532.hnf);
                          primops = (uu___150_10532.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_10532.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_10532.unfold_until);
                          unfold_only = (uu___150_10532.unfold_only);
                          unfold_fully = (uu___150_10532.unfold_fully);
                          unfold_attr = (uu___150_10532.unfold_attr);
                          unfold_tac = (uu___150_10532.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_10532.pure_subterms_within_computations);
                          simplify = (uu___150_10532.simplify);
                          erase_universes = (uu___150_10532.erase_universes);
                          allow_unbound_universes =
                            (uu___150_10532.allow_unbound_universes);
                          reify_ = (uu___150_10532.reify_);
                          compress_uvars = (uu___150_10532.compress_uvars);
                          no_full_norm = (uu___150_10532.no_full_norm);
                          check_no_uvars = (uu___150_10532.check_no_uvars);
                          unmeta = (uu___150_10532.unmeta);
                          unascribe = (uu___150_10532.unascribe);
                          in_full_norm_request = true
                        }  in
                      {
                        steps = uu____10531;
                        tcenv = (uu___149_10530.tcenv);
                        debug = (uu___149_10530.debug);
                        delta_level;
                        primitive_steps = (uu___149_10530.primitive_steps);
                        strong = (uu___149_10530.strong);
                        memoize_lazy = (uu___149_10530.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10541 =
                          let uu____10542 =
                            let uu____10547 = FStar_Util.now ()  in
                            (t1, uu____10547)  in
                          Debug uu____10542  in
                        uu____10541 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10551 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10551
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10560 =
                      let uu____10567 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10567, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10560  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10577 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10577  in
               let uu____10578 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10578
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10584  ->
                       let uu____10585 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10586 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10585 uu____10586);
                  if b
                  then
                    (let uu____10587 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10587 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10595 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10595) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10601  ->
                               match uu___89_10601 with
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
                          (let uu____10611 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10611))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10630) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10665,uu____10666) -> false)))
                     in
                  let uu____10683 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____10699 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____10699 then (true, true) else (false, false)
                     in
                  match uu____10683 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____10712  ->
                            let uu____10713 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____10714 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____10715 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____10713 uu____10714 uu____10715);
                       if should_delta2
                       then
                         (let uu____10716 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_10732 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_10735 = cfg.steps  in
                                      {
                                        beta = (uu___152_10735.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_10735.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_10735.unfold_attr);
                                        unfold_tac =
                                          (uu___152_10735.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_10735.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_10735.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_10735.allow_unbound_universes);
                                        reify_ = (uu___152_10735.reify_);
                                        compress_uvars =
                                          (uu___152_10735.compress_uvars);
                                        no_full_norm =
                                          (uu___152_10735.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_10735.check_no_uvars);
                                        unmeta = (uu___152_10735.unmeta);
                                        unascribe =
                                          (uu___152_10735.unascribe);
                                        in_full_norm_request =
                                          (uu___152_10735.in_full_norm_request)
                                      });
                                   tcenv = (uu___151_10732.tcenv);
                                   debug = (uu___151_10732.debug);
                                   delta_level = (uu___151_10732.delta_level);
                                   primitive_steps =
                                     (uu___151_10732.primitive_steps);
                                   strong = (uu___151_10732.strong);
                                   memoize_lazy =
                                     (uu___151_10732.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_10732.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____10716 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10749 = lookup_bvar env x  in
               (match uu____10749 with
                | Univ uu____10750 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10799 = FStar_ST.op_Bang r  in
                      (match uu____10799 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10917  ->
                                 let uu____10918 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10919 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10918
                                   uu____10919);
                            (let uu____10920 =
                               let uu____10921 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10921.FStar_Syntax_Syntax.n  in
                             match uu____10920 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10924 ->
                                 norm cfg env2 stack t'
                             | uu____10941 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11011)::uu____11012 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11021)::uu____11022 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11034,uu____11035))::stack_rest ->
                    (match c with
                     | Univ uu____11039 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11048 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11069  ->
                                    let uu____11070 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11070);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11110  ->
                                    let uu____11111 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11111);
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
                       (fun uu____11189  ->
                          let uu____11190 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11190);
                     norm cfg env stack1 t1)
                | (Debug uu____11191)::uu____11192 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11202 = cfg.steps  in
                             {
                               beta = (uu___153_11202.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11202.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11202.unfold_until);
                               unfold_only = (uu___153_11202.unfold_only);
                               unfold_fully = (uu___153_11202.unfold_fully);
                               unfold_attr = (uu___153_11202.unfold_attr);
                               unfold_tac = (uu___153_11202.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11202.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11202.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11202.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11202.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11202.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11204 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11204.tcenv);
                               debug = (uu___154_11204.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11204.primitive_steps);
                               strong = (uu___154_11204.strong);
                               memoize_lazy = (uu___154_11204.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11204.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11206 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11206 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11248  -> dummy :: env1) env)
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
                                          let uu____11285 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11285)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11290 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11290.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11290.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11291 -> lopt  in
                           (log cfg
                              (fun uu____11297  ->
                                 let uu____11298 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11298);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11307 = cfg  in
                               {
                                 steps = (uu___156_11307.steps);
                                 tcenv = (uu___156_11307.tcenv);
                                 debug = (uu___156_11307.debug);
                                 delta_level = (uu___156_11307.delta_level);
                                 primitive_steps =
                                   (uu___156_11307.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11307.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11307.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11318)::uu____11319 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11331 = cfg.steps  in
                             {
                               beta = (uu___153_11331.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11331.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11331.unfold_until);
                               unfold_only = (uu___153_11331.unfold_only);
                               unfold_fully = (uu___153_11331.unfold_fully);
                               unfold_attr = (uu___153_11331.unfold_attr);
                               unfold_tac = (uu___153_11331.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11331.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11331.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11331.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11331.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11331.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11333 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11333.tcenv);
                               debug = (uu___154_11333.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11333.primitive_steps);
                               strong = (uu___154_11333.strong);
                               memoize_lazy = (uu___154_11333.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11333.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11335 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11335 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11377  -> dummy :: env1) env)
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
                                          let uu____11414 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11414)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11419 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11419.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11419.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11420 -> lopt  in
                           (log cfg
                              (fun uu____11426  ->
                                 let uu____11427 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11427);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11436 = cfg  in
                               {
                                 steps = (uu___156_11436.steps);
                                 tcenv = (uu___156_11436.tcenv);
                                 debug = (uu___156_11436.debug);
                                 delta_level = (uu___156_11436.delta_level);
                                 primitive_steps =
                                   (uu___156_11436.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11436.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11436.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11447)::uu____11448 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11462 = cfg.steps  in
                             {
                               beta = (uu___153_11462.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11462.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11462.unfold_until);
                               unfold_only = (uu___153_11462.unfold_only);
                               unfold_fully = (uu___153_11462.unfold_fully);
                               unfold_attr = (uu___153_11462.unfold_attr);
                               unfold_tac = (uu___153_11462.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11462.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11462.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11462.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11462.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11462.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11464 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11464.tcenv);
                               debug = (uu___154_11464.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11464.primitive_steps);
                               strong = (uu___154_11464.strong);
                               memoize_lazy = (uu___154_11464.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11464.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11466 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11466 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11508  -> dummy :: env1) env)
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
                                          let uu____11545 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11545)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11550 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11550.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11550.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11551 -> lopt  in
                           (log cfg
                              (fun uu____11557  ->
                                 let uu____11558 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11558);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11567 = cfg  in
                               {
                                 steps = (uu___156_11567.steps);
                                 tcenv = (uu___156_11567.tcenv);
                                 debug = (uu___156_11567.debug);
                                 delta_level = (uu___156_11567.delta_level);
                                 primitive_steps =
                                   (uu___156_11567.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11567.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11567.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11578)::uu____11579 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11593 = cfg.steps  in
                             {
                               beta = (uu___153_11593.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11593.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11593.unfold_until);
                               unfold_only = (uu___153_11593.unfold_only);
                               unfold_fully = (uu___153_11593.unfold_fully);
                               unfold_attr = (uu___153_11593.unfold_attr);
                               unfold_tac = (uu___153_11593.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11593.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11593.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11593.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11593.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11593.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11595 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11595.tcenv);
                               debug = (uu___154_11595.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11595.primitive_steps);
                               strong = (uu___154_11595.strong);
                               memoize_lazy = (uu___154_11595.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11595.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11597 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11597 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11639  -> dummy :: env1) env)
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
                                          let uu____11676 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11676)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11681 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11681.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11681.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11682 -> lopt  in
                           (log cfg
                              (fun uu____11688  ->
                                 let uu____11689 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11689);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11698 = cfg  in
                               {
                                 steps = (uu___156_11698.steps);
                                 tcenv = (uu___156_11698.tcenv);
                                 debug = (uu___156_11698.debug);
                                 delta_level = (uu___156_11698.delta_level);
                                 primitive_steps =
                                   (uu___156_11698.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11698.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11698.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11709)::uu____11710 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11728 = cfg.steps  in
                             {
                               beta = (uu___153_11728.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11728.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11728.unfold_until);
                               unfold_only = (uu___153_11728.unfold_only);
                               unfold_fully = (uu___153_11728.unfold_fully);
                               unfold_attr = (uu___153_11728.unfold_attr);
                               unfold_tac = (uu___153_11728.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11728.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11728.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11728.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11728.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11728.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11730 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11730.tcenv);
                               debug = (uu___154_11730.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11730.primitive_steps);
                               strong = (uu___154_11730.strong);
                               memoize_lazy = (uu___154_11730.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11730.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11732 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11732 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11774  -> dummy :: env1) env)
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
                                          let uu____11811 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11811)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11816 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11816.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11816.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11817 -> lopt  in
                           (log cfg
                              (fun uu____11823  ->
                                 let uu____11824 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11824);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11833 = cfg  in
                               {
                                 steps = (uu___156_11833.steps);
                                 tcenv = (uu___156_11833.tcenv);
                                 debug = (uu___156_11833.debug);
                                 delta_level = (uu___156_11833.delta_level);
                                 primitive_steps =
                                   (uu___156_11833.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11833.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11833.normalize_pure_lets)
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
                             let uu___153_11847 = cfg.steps  in
                             {
                               beta = (uu___153_11847.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11847.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11847.unfold_until);
                               unfold_only = (uu___153_11847.unfold_only);
                               unfold_fully = (uu___153_11847.unfold_fully);
                               unfold_attr = (uu___153_11847.unfold_attr);
                               unfold_tac = (uu___153_11847.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11847.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11847.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11847.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11847.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11847.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_11849 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11849.tcenv);
                               debug = (uu___154_11849.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11849.primitive_steps);
                               strong = (uu___154_11849.strong);
                               memoize_lazy = (uu___154_11849.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11849.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11851 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11851 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11893  -> dummy :: env1) env)
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
                                          let uu____11930 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11930)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11935 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11935.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11935.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11936 -> lopt  in
                           (log cfg
                              (fun uu____11942  ->
                                 let uu____11943 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11943);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11952 = cfg  in
                               {
                                 steps = (uu___156_11952.steps);
                                 tcenv = (uu___156_11952.tcenv);
                                 debug = (uu___156_11952.debug);
                                 delta_level = (uu___156_11952.delta_level);
                                 primitive_steps =
                                   (uu___156_11952.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11952.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11952.normalize_pure_lets)
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
                      (fun uu____12001  ->
                         fun stack1  ->
                           match uu____12001 with
                           | (a,aq) ->
                               let uu____12013 =
                                 let uu____12014 =
                                   let uu____12021 =
                                     let uu____12022 =
                                       let uu____12053 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12053, false)  in
                                     Clos uu____12022  in
                                   (uu____12021, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12014  in
                               uu____12013 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12137  ->
                     let uu____12138 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12138);
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
                             ((let uu___157_12174 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12174.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12174.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12175 ->
                      let uu____12180 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12180)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12183 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12183 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12214 =
                          let uu____12215 =
                            let uu____12222 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_12224 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_12224.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_12224.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12222)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12215  in
                        mk uu____12214 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12243 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12243
               else
                 (let uu____12245 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12245 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12253 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12277  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12253 c1  in
                      let t2 =
                        let uu____12299 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12299 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12410)::uu____12411 ->
                    (log cfg
                       (fun uu____12424  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12425)::uu____12426 ->
                    (log cfg
                       (fun uu____12437  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12438,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12439;
                                   FStar_Syntax_Syntax.vars = uu____12440;_},uu____12441,uu____12442))::uu____12443
                    ->
                    (log cfg
                       (fun uu____12452  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12453)::uu____12454 ->
                    (log cfg
                       (fun uu____12465  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12466 ->
                    (log cfg
                       (fun uu____12469  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____12473  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12490 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12490
                         | FStar_Util.Inr c ->
                             let uu____12498 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12498
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12511 =
                               let uu____12512 =
                                 let uu____12539 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12539, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12512
                                in
                             mk uu____12511 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12558 ->
                           let uu____12559 =
                             let uu____12560 =
                               let uu____12561 =
                                 let uu____12588 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12588, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12561
                                in
                             mk uu____12560 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12559))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if (cfg.steps).iota
                 then
                   let uu___159_12665 = cfg  in
                   {
                     steps =
                       (let uu___160_12668 = cfg.steps  in
                        {
                          beta = (uu___160_12668.beta);
                          iota = (uu___160_12668.iota);
                          zeta = (uu___160_12668.zeta);
                          weak = true;
                          hnf = (uu___160_12668.hnf);
                          primops = (uu___160_12668.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_12668.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_12668.unfold_until);
                          unfold_only = (uu___160_12668.unfold_only);
                          unfold_fully = (uu___160_12668.unfold_fully);
                          unfold_attr = (uu___160_12668.unfold_attr);
                          unfold_tac = (uu___160_12668.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_12668.pure_subterms_within_computations);
                          simplify = (uu___160_12668.simplify);
                          erase_universes = (uu___160_12668.erase_universes);
                          allow_unbound_universes =
                            (uu___160_12668.allow_unbound_universes);
                          reify_ = (uu___160_12668.reify_);
                          compress_uvars = (uu___160_12668.compress_uvars);
                          no_full_norm = (uu___160_12668.no_full_norm);
                          check_no_uvars = (uu___160_12668.check_no_uvars);
                          unmeta = (uu___160_12668.unmeta);
                          unascribe = (uu___160_12668.unascribe);
                          in_full_norm_request =
                            (uu___160_12668.in_full_norm_request)
                        });
                     tcenv = (uu___159_12665.tcenv);
                     debug = (uu___159_12665.debug);
                     delta_level = (uu___159_12665.delta_level);
                     primitive_steps = (uu___159_12665.primitive_steps);
                     strong = (uu___159_12665.strong);
                     memoize_lazy = (uu___159_12665.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_12665.normalize_pure_lets)
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
                         let uu____12704 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12704 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_12724 = cfg  in
                               let uu____12725 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_12724.steps);
                                 tcenv = uu____12725;
                                 debug = (uu___161_12724.debug);
                                 delta_level = (uu___161_12724.delta_level);
                                 primitive_steps =
                                   (uu___161_12724.primitive_steps);
                                 strong = (uu___161_12724.strong);
                                 memoize_lazy = (uu___161_12724.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_12724.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12730 =
                                 let uu____12731 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12731  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12730
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_12734 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_12734.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_12734.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_12734.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_12734.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12735 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12735
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12746,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12747;
                               FStar_Syntax_Syntax.lbunivs = uu____12748;
                               FStar_Syntax_Syntax.lbtyp = uu____12749;
                               FStar_Syntax_Syntax.lbeff = uu____12750;
                               FStar_Syntax_Syntax.lbdef = uu____12751;
                               FStar_Syntax_Syntax.lbattrs = uu____12752;
                               FStar_Syntax_Syntax.lbpos = uu____12753;_}::uu____12754),uu____12755)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12795 =
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
               if uu____12795
               then
                 let binder =
                   let uu____12797 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12797  in
                 let env1 =
                   let uu____12807 =
                     let uu____12814 =
                       let uu____12815 =
                         let uu____12846 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12846,
                           false)
                          in
                       Clos uu____12815  in
                     ((FStar_Pervasives_Native.Some binder), uu____12814)  in
                   uu____12807 :: env  in
                 (log cfg
                    (fun uu____12939  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12943  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12944 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12944))
                 else
                   (let uu____12946 =
                      let uu____12951 =
                        let uu____12952 =
                          let uu____12953 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12953
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12952]  in
                      FStar_Syntax_Subst.open_term uu____12951 body  in
                    match uu____12946 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12962  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12970 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12970  in
                            FStar_Util.Inl
                              (let uu___163_12980 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_12980.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_12980.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12983  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_12985 = lb  in
                             let uu____12986 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_12985.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_12985.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12986;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_12985.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_12985.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13021  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_13044 = cfg  in
                             {
                               steps = (uu___165_13044.steps);
                               tcenv = (uu___165_13044.tcenv);
                               debug = (uu___165_13044.debug);
                               delta_level = (uu___165_13044.delta_level);
                               primitive_steps =
                                 (uu___165_13044.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_13044.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_13044.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13047  ->
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
               let uu____13064 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13064 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13100 =
                               let uu___166_13101 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_13101.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_13101.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13100  in
                           let uu____13102 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13102 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13128 =
                                   FStar_List.map (fun uu____13144  -> dummy)
                                     lbs1
                                    in
                                 let uu____13145 =
                                   let uu____13154 =
                                     FStar_List.map
                                       (fun uu____13174  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13154 env  in
                                 FStar_List.append uu____13128 uu____13145
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13198 =
                                       let uu___167_13199 = rc  in
                                       let uu____13200 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_13199.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13200;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_13199.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13198
                                 | uu____13207 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_13211 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_13211.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_13211.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_13211.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_13211.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13221 =
                        FStar_List.map (fun uu____13237  -> dummy) lbs2  in
                      FStar_List.append uu____13221 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13245 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13245 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_13261 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_13261.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_13261.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13288 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13288
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13307 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13383  ->
                        match uu____13383 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_13504 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_13504.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_13504.FStar_Syntax_Syntax.sort)
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
               (match uu____13307 with
                | (rec_env,memos,uu____13717) ->
                    let uu____13770 =
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
                             let uu____14081 =
                               let uu____14088 =
                                 let uu____14089 =
                                   let uu____14120 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14120, false)
                                    in
                                 Clos uu____14089  in
                               (FStar_Pervasives_Native.None, uu____14088)
                                in
                             uu____14081 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14230  ->
                     let uu____14231 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14231);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14253 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14255::uu____14256 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14261) ->
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
                             | uu____14284 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14298 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14298
                              | uu____14309 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14313 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14339 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14357 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14374 =
                        let uu____14375 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14376 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14375 uu____14376
                         in
                      failwith uu____14374
                    else rebuild cfg env stack t2
                | uu____14378 -> norm cfg env stack t2))

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
                let uu____14388 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14388  in
              let uu____14389 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14389 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14402  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((true ,uu____14409),uu____14410);
                           FStar_Syntax_Syntax.sigrng = uu____14411;
                           FStar_Syntax_Syntax.sigquals = uu____14412;
                           FStar_Syntax_Syntax.sigmeta = uu____14413;
                           FStar_Syntax_Syntax.sigattrs = uu____14414;_},uu____14415),uu____14416)
                       when Prims.op_Negation (cfg.steps).zeta ->
                       rebuild cfg env stack t0
                   | uu____14481 ->
                       (log cfg
                          (fun uu____14486  ->
                             let uu____14487 =
                               FStar_Syntax_Print.term_to_string t0  in
                             let uu____14488 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____14487 uu____14488);
                        (let t1 =
                           if
                             ((cfg.steps).unfold_until =
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Delta_constant))
                               && (Prims.op_Negation (cfg.steps).unfold_tac)
                           then t
                           else
                             (let uu____14493 =
                                FStar_Ident.range_of_lid
                                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                 in
                              FStar_Syntax_Subst.set_use_range uu____14493 t)
                            in
                         let n1 = FStar_List.length us  in
                         if n1 > (Prims.parse_int "0")
                         then
                           match stack with
                           | (UnivArgs (us',uu____14502))::stack1 ->
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
                           | uu____14557 when
                               (cfg.steps).erase_universes ||
                                 (cfg.steps).allow_unbound_universes
                               -> norm cfg env stack t1
                           | uu____14560 ->
                               let uu____14563 =
                                 let uu____14564 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____14564
                                  in
                               failwith uu____14563
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
                  let uu___171_14588 = cfg  in
                  let uu____14589 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____14589;
                    tcenv = (uu___171_14588.tcenv);
                    debug = (uu___171_14588.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_14588.primitive_steps);
                    strong = (uu___171_14588.strong);
                    memoize_lazy = (uu___171_14588.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_14588.normalize_pure_lets)
                  }
                else
                  (let uu___172_14591 = cfg  in
                   {
                     steps =
                       (let uu___173_14594 = cfg.steps  in
                        {
                          beta = (uu___173_14594.beta);
                          iota = (uu___173_14594.iota);
                          zeta = false;
                          weak = (uu___173_14594.weak);
                          hnf = (uu___173_14594.hnf);
                          primops = (uu___173_14594.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_14594.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_14594.unfold_until);
                          unfold_only = (uu___173_14594.unfold_only);
                          unfold_fully = (uu___173_14594.unfold_fully);
                          unfold_attr = (uu___173_14594.unfold_attr);
                          unfold_tac = (uu___173_14594.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_14594.pure_subterms_within_computations);
                          simplify = (uu___173_14594.simplify);
                          erase_universes = (uu___173_14594.erase_universes);
                          allow_unbound_universes =
                            (uu___173_14594.allow_unbound_universes);
                          reify_ = (uu___173_14594.reify_);
                          compress_uvars = (uu___173_14594.compress_uvars);
                          no_full_norm = (uu___173_14594.no_full_norm);
                          check_no_uvars = (uu___173_14594.check_no_uvars);
                          unmeta = (uu___173_14594.unmeta);
                          unascribe = (uu___173_14594.unascribe);
                          in_full_norm_request =
                            (uu___173_14594.in_full_norm_request)
                        });
                     tcenv = (uu___172_14591.tcenv);
                     debug = (uu___172_14591.debug);
                     delta_level = (uu___172_14591.delta_level);
                     primitive_steps = (uu___172_14591.primitive_steps);
                     strong = (uu___172_14591.strong);
                     memoize_lazy = (uu___172_14591.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_14591.normalize_pure_lets)
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
                  (fun uu____14624  ->
                     let uu____14625 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____14626 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14625
                       uu____14626);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____14628 =
                   let uu____14629 = FStar_Syntax_Subst.compress head3  in
                   uu____14629.FStar_Syntax_Syntax.n  in
                 match uu____14628 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____14647 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14647
                        in
                     let uu____14648 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14648 with
                      | (uu____14649,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14655 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14663 =
                                   let uu____14664 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____14664.FStar_Syntax_Syntax.n  in
                                 match uu____14663 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14670,uu____14671))
                                     ->
                                     let uu____14680 =
                                       let uu____14681 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____14681.FStar_Syntax_Syntax.n  in
                                     (match uu____14680 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14687,msrc,uu____14689))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14698 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14698
                                      | uu____14699 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14700 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14701 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14701 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_14706 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_14706.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_14706.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_14706.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_14706.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_14706.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14707 = FStar_List.tl stack  in
                                    let uu____14708 =
                                      let uu____14709 =
                                        let uu____14712 =
                                          let uu____14713 =
                                            let uu____14726 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14726)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14713
                                           in
                                        FStar_Syntax_Syntax.mk uu____14712
                                         in
                                      uu____14709
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14707 uu____14708
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14742 =
                                      let uu____14743 = is_return body  in
                                      match uu____14743 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14747;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14748;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14753 -> false  in
                                    if uu____14742
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
                                         let uu____14776 =
                                           let uu____14779 =
                                             let uu____14780 =
                                               let uu____14797 =
                                                 let uu____14800 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14800]  in
                                               (uu____14797, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14780
                                              in
                                           FStar_Syntax_Syntax.mk uu____14779
                                            in
                                         uu____14776
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14816 =
                                           let uu____14817 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14817.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14816 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14823::uu____14824::[])
                                             ->
                                             let uu____14831 =
                                               let uu____14834 =
                                                 let uu____14835 =
                                                   let uu____14842 =
                                                     let uu____14845 =
                                                       let uu____14846 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14846
                                                        in
                                                     let uu____14847 =
                                                       let uu____14850 =
                                                         let uu____14851 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14851
                                                          in
                                                       [uu____14850]  in
                                                     uu____14845 ::
                                                       uu____14847
                                                      in
                                                   (bind1, uu____14842)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14835
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14834
                                                in
                                             uu____14831
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14859 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14865 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14865
                                         then
                                           let uu____14868 =
                                             let uu____14869 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14869
                                              in
                                           let uu____14870 =
                                             let uu____14873 =
                                               let uu____14874 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14874
                                                in
                                             [uu____14873]  in
                                           uu____14868 :: uu____14870
                                         else []  in
                                       let reified =
                                         let uu____14879 =
                                           let uu____14882 =
                                             let uu____14883 =
                                               let uu____14898 =
                                                 let uu____14901 =
                                                   let uu____14904 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14905 =
                                                     let uu____14908 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14908]  in
                                                   uu____14904 :: uu____14905
                                                    in
                                                 let uu____14909 =
                                                   let uu____14912 =
                                                     let uu____14915 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14916 =
                                                       let uu____14919 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14920 =
                                                         let uu____14923 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14924 =
                                                           let uu____14927 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14927]  in
                                                         uu____14923 ::
                                                           uu____14924
                                                          in
                                                       uu____14919 ::
                                                         uu____14920
                                                        in
                                                     uu____14915 ::
                                                       uu____14916
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14912
                                                    in
                                                 FStar_List.append
                                                   uu____14901 uu____14909
                                                  in
                                               (bind_inst, uu____14898)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14883
                                              in
                                           FStar_Syntax_Syntax.mk uu____14882
                                            in
                                         uu____14879
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14939  ->
                                            let uu____14940 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14941 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14940 uu____14941);
                                       (let uu____14942 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14942 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14966 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14966
                        in
                     let uu____14967 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14967 with
                      | (uu____14968,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15003 =
                                  let uu____15004 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15004.FStar_Syntax_Syntax.n  in
                                match uu____15003 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15010) -> t2
                                | uu____15015 -> head4  in
                              let uu____15016 =
                                let uu____15017 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15017.FStar_Syntax_Syntax.n  in
                              match uu____15016 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15023 -> FStar_Pervasives_Native.None
                               in
                            let uu____15024 = maybe_extract_fv head4  in
                            match uu____15024 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15034 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15034
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____15039 = maybe_extract_fv head5
                                     in
                                  match uu____15039 with
                                  | FStar_Pervasives_Native.Some uu____15044
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15045 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____15050 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15065 =
                              match uu____15065 with
                              | (e,q) ->
                                  let uu____15072 =
                                    let uu____15073 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15073.FStar_Syntax_Syntax.n  in
                                  (match uu____15072 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____15088 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____15088
                                   | uu____15089 -> false)
                               in
                            let uu____15090 =
                              let uu____15091 =
                                let uu____15098 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15098 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15091
                               in
                            if uu____15090
                            then
                              let uu____15103 =
                                let uu____15104 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15104
                                 in
                              failwith uu____15103
                            else ());
                           (let uu____15106 = maybe_unfold_action head_app
                               in
                            match uu____15106 with
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
                                   (fun uu____15147  ->
                                      let uu____15148 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15149 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15148 uu____15149);
                                 (let uu____15150 = FStar_List.tl stack  in
                                  norm cfg env uu____15150 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15152) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15176 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15176  in
                     (log cfg
                        (fun uu____15180  ->
                           let uu____15181 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15181);
                      (let uu____15182 = FStar_List.tl stack  in
                       norm cfg env uu____15182 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15303  ->
                               match uu____15303 with
                               | (pat,wopt,tm) ->
                                   let uu____15351 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15351)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15383 = FStar_List.tl stack  in
                     norm cfg env uu____15383 tm
                 | uu____15384 -> fallback ())

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
              (fun uu____15398  ->
                 let uu____15399 = FStar_Ident.string_of_lid msrc  in
                 let uu____15400 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15401 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15399
                   uu____15400 uu____15401);
            (let uu____15402 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15402
             then
               let ed =
                 let uu____15404 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15404  in
               let uu____15405 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15405 with
               | (uu____15406,return_repr) ->
                   let return_inst =
                     let uu____15415 =
                       let uu____15416 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15416.FStar_Syntax_Syntax.n  in
                     match uu____15415 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15422::[]) ->
                         let uu____15429 =
                           let uu____15432 =
                             let uu____15433 =
                               let uu____15440 =
                                 let uu____15443 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15443]  in
                               (return_tm, uu____15440)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15433  in
                           FStar_Syntax_Syntax.mk uu____15432  in
                         uu____15429 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15451 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15454 =
                     let uu____15457 =
                       let uu____15458 =
                         let uu____15473 =
                           let uu____15476 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15477 =
                             let uu____15480 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15480]  in
                           uu____15476 :: uu____15477  in
                         (return_inst, uu____15473)  in
                       FStar_Syntax_Syntax.Tm_app uu____15458  in
                     FStar_Syntax_Syntax.mk uu____15457  in
                   uu____15454 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15489 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15489 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15492 =
                      let uu____15493 = FStar_Ident.text_of_lid msrc  in
                      let uu____15494 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15493 uu____15494
                       in
                    failwith uu____15492
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15495;
                      FStar_TypeChecker_Env.mtarget = uu____15496;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15497;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15512 =
                      let uu____15513 = FStar_Ident.text_of_lid msrc  in
                      let uu____15514 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15513 uu____15514
                       in
                    failwith uu____15512
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15515;
                      FStar_TypeChecker_Env.mtarget = uu____15516;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15517;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15541 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15542 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15541 t FStar_Syntax_Syntax.tun uu____15542))

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
                (fun uu____15598  ->
                   match uu____15598 with
                   | (a,imp) ->
                       let uu____15609 = norm cfg env [] a  in
                       (uu____15609, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____15617  ->
             let uu____15618 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____15619 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____15618 uu____15619);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15643 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                     uu____15643
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_15646 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_15646.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_15646.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15666 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____15666
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_15669 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_15669.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_15669.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15702  ->
                      match uu____15702 with
                      | (a,i) ->
                          let uu____15713 = norm cfg env [] a  in
                          (uu____15713, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_15731  ->
                       match uu___90_15731 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15735 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15735
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_15743 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_15746 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_15746.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_15743.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_15743.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15749  ->
        match uu____15749 with
        | (x,imp) ->
            let uu____15752 =
              let uu___179_15753 = x  in
              let uu____15754 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_15753.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_15753.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15754
              }  in
            (uu____15752, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15760 =
          FStar_List.fold_left
            (fun uu____15778  ->
               fun b  ->
                 match uu____15778 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15760 with | (nbs,uu____15818) -> FStar_List.rev nbs

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
            let uu____15834 =
              let uu___180_15835 = rc  in
              let uu____15836 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_15835.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15836;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_15835.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15834
        | uu____15843 -> lopt

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
            (let uu____15864 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15865 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15864
               uu____15865)
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
          let uu____15885 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15885
          then tm1
          else
            (let w t =
               let uu___181_15897 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_15897.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_15897.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15906 =
                 let uu____15907 = FStar_Syntax_Util.unmeta t  in
                 uu____15907.FStar_Syntax_Syntax.n  in
               match uu____15906 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15914 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15959)::args1,(bv,uu____15962)::bs1) ->
                   let uu____15996 =
                     let uu____15997 = FStar_Syntax_Subst.compress t  in
                     uu____15997.FStar_Syntax_Syntax.n  in
                   (match uu____15996 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16001 -> false)
               | ([],[]) -> true
               | (uu____16022,uu____16023) -> false  in
             let is_applied bs t =
               let uu____16059 = FStar_Syntax_Util.head_and_args' t  in
               match uu____16059 with
               | (hd1,args) ->
                   let uu____16092 =
                     let uu____16093 = FStar_Syntax_Subst.compress hd1  in
                     uu____16093.FStar_Syntax_Syntax.n  in
                   (match uu____16092 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____16099 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____16111 = FStar_Syntax_Util.is_squash t  in
               match uu____16111 with
               | FStar_Pervasives_Native.Some (uu____16122,t') ->
                   is_applied bs t'
               | uu____16134 ->
                   let uu____16143 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____16143 with
                    | FStar_Pervasives_Native.Some (uu____16154,t') ->
                        is_applied bs t'
                    | uu____16166 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____16183 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16183 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16190)::(q,uu____16192)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____16227 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____16227 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____16232 =
                          let uu____16233 = FStar_Syntax_Subst.compress p  in
                          uu____16233.FStar_Syntax_Syntax.n  in
                        (match uu____16232 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16239 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____16239
                         | uu____16240 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____16243)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____16268 =
                          let uu____16269 = FStar_Syntax_Subst.compress p1
                             in
                          uu____16269.FStar_Syntax_Syntax.n  in
                        (match uu____16268 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16275 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____16275
                         | uu____16276 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____16280 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____16280 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____16285 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____16285 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16292 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16292
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____16295)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16320 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____16320 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16327 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16327
                              | uu____16328 -> FStar_Pervasives_Native.None)
                         | uu____16331 -> FStar_Pervasives_Native.None)
                    | uu____16334 -> FStar_Pervasives_Native.None)
               | uu____16337 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16348 =
                 let uu____16349 = FStar_Syntax_Subst.compress phi  in
                 uu____16349.FStar_Syntax_Syntax.n  in
               match uu____16348 with
               | FStar_Syntax_Syntax.Tm_match (uu____16354,br::brs) ->
                   let uu____16421 = br  in
                   (match uu____16421 with
                    | (uu____16438,uu____16439,e) ->
                        let r =
                          let uu____16460 = simp_t e  in
                          match uu____16460 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16466 =
                                FStar_List.for_all
                                  (fun uu____16484  ->
                                     match uu____16484 with
                                     | (uu____16497,uu____16498,e') ->
                                         let uu____16512 = simp_t e'  in
                                         uu____16512 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16466
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16520 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16525 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16525
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16546 =
                 match uu____16546 with
                 | (t1,q) ->
                     let uu____16559 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____16559 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____16587 -> (t1, q))
                  in
               let uu____16596 = FStar_Syntax_Util.head_and_args t  in
               match uu____16596 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16658 =
                 let uu____16659 = FStar_Syntax_Util.unmeta ty  in
                 uu____16659.FStar_Syntax_Syntax.n  in
               match uu____16658 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16663) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16668,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16688 -> false  in
             let simplify1 arg =
               let uu____16711 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16711, arg)  in
             let uu____16720 = is_quantified_const tm1  in
             match uu____16720 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16724 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16724
             | FStar_Pervasives_Native.None  ->
                 let uu____16725 =
                   let uu____16726 = FStar_Syntax_Subst.compress tm1  in
                   uu____16726.FStar_Syntax_Syntax.n  in
                 (match uu____16725 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16730;
                              FStar_Syntax_Syntax.vars = uu____16731;_},uu____16732);
                         FStar_Syntax_Syntax.pos = uu____16733;
                         FStar_Syntax_Syntax.vars = uu____16734;_},args)
                      ->
                      let uu____16760 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16760
                      then
                        let uu____16761 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16761 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16808)::
                             (uu____16809,(arg,uu____16811))::[] ->
                             maybe_auto_squash arg
                         | (uu____16860,(arg,uu____16862))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16863)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16912)::uu____16913::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16964::(FStar_Pervasives_Native.Some (false
                                         ),uu____16965)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17016 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17030 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17030
                         then
                           let uu____17031 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17031 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17078)::uu____17079::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17130::(FStar_Pervasives_Native.Some (true
                                           ),uu____17131)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17182)::(uu____17183,(arg,uu____17185))::[]
                               -> maybe_auto_squash arg
                           | (uu____17234,(arg,uu____17236))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17237)::[]
                               -> maybe_auto_squash arg
                           | uu____17286 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17300 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17300
                            then
                              let uu____17301 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17301 with
                              | uu____17348::(FStar_Pervasives_Native.Some
                                              (true ),uu____17349)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17400)::uu____17401::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17452)::(uu____17453,(arg,uu____17455))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17504,(p,uu____17506))::(uu____17507,
                                                                (q,uu____17509))::[]
                                  ->
                                  let uu____17556 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17556
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17558 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17572 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17572
                               then
                                 let uu____17573 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17573 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17620)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17621)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17672)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17673)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17724)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17725)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17776)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17777)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17828,(arg,uu____17830))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17831)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17880)::(uu____17881,(arg,uu____17883))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17932,(arg,uu____17934))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17935)::[]
                                     ->
                                     let uu____17984 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17984
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17985)::(uu____17986,(arg,uu____17988))::[]
                                     ->
                                     let uu____18037 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18037
                                 | (uu____18038,(p,uu____18040))::(uu____18041,
                                                                   (q,uu____18043))::[]
                                     ->
                                     let uu____18090 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18090
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18092 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18106 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18106
                                  then
                                    let uu____18107 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18107 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18154)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18185)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18216 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18230 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18230
                                     then
                                       match args with
                                       | (t,uu____18232)::[] ->
                                           let uu____18249 =
                                             let uu____18250 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18250.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18249 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18253::[],body,uu____18255)
                                                ->
                                                let uu____18282 = simp_t body
                                                   in
                                                (match uu____18282 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18285 -> tm1)
                                            | uu____18288 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18290))::(t,uu____18292)::[]
                                           ->
                                           let uu____18331 =
                                             let uu____18332 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18332.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18331 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18335::[],body,uu____18337)
                                                ->
                                                let uu____18364 = simp_t body
                                                   in
                                                (match uu____18364 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18367 -> tm1)
                                            | uu____18370 -> tm1)
                                       | uu____18371 -> tm1
                                     else
                                       (let uu____18381 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18381
                                        then
                                          match args with
                                          | (t,uu____18383)::[] ->
                                              let uu____18400 =
                                                let uu____18401 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18401.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18400 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18404::[],body,uu____18406)
                                                   ->
                                                   let uu____18433 =
                                                     simp_t body  in
                                                   (match uu____18433 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18436 -> tm1)
                                               | uu____18439 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18441))::(t,uu____18443)::[]
                                              ->
                                              let uu____18482 =
                                                let uu____18483 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18483.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18482 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18486::[],body,uu____18488)
                                                   ->
                                                   let uu____18515 =
                                                     simp_t body  in
                                                   (match uu____18515 with
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
                                                    | uu____18518 -> tm1)
                                               | uu____18521 -> tm1)
                                          | uu____18522 -> tm1
                                        else
                                          (let uu____18532 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18532
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18533;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18534;_},uu____18535)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18552;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18553;_},uu____18554)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18571 -> tm1
                                           else
                                             (let uu____18581 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18581 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18601 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18611;
                         FStar_Syntax_Syntax.vars = uu____18612;_},args)
                      ->
                      let uu____18634 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18634
                      then
                        let uu____18635 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18635 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18682)::
                             (uu____18683,(arg,uu____18685))::[] ->
                             maybe_auto_squash arg
                         | (uu____18734,(arg,uu____18736))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18737)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18786)::uu____18787::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18838::(FStar_Pervasives_Native.Some (false
                                         ),uu____18839)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18890 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18904 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18904
                         then
                           let uu____18905 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18905 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18952)::uu____18953::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19004::(FStar_Pervasives_Native.Some (true
                                           ),uu____19005)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19056)::(uu____19057,(arg,uu____19059))::[]
                               -> maybe_auto_squash arg
                           | (uu____19108,(arg,uu____19110))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19111)::[]
                               -> maybe_auto_squash arg
                           | uu____19160 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19174 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19174
                            then
                              let uu____19175 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19175 with
                              | uu____19222::(FStar_Pervasives_Native.Some
                                              (true ),uu____19223)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19274)::uu____19275::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19326)::(uu____19327,(arg,uu____19329))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19378,(p,uu____19380))::(uu____19381,
                                                                (q,uu____19383))::[]
                                  ->
                                  let uu____19430 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19430
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19432 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19446 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19446
                               then
                                 let uu____19447 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19447 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19494)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19495)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19546)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19547)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19598)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19599)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19650)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19651)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19702,(arg,uu____19704))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19705)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19754)::(uu____19755,(arg,uu____19757))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19806,(arg,uu____19808))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19809)::[]
                                     ->
                                     let uu____19858 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19858
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19859)::(uu____19860,(arg,uu____19862))::[]
                                     ->
                                     let uu____19911 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19911
                                 | (uu____19912,(p,uu____19914))::(uu____19915,
                                                                   (q,uu____19917))::[]
                                     ->
                                     let uu____19964 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19964
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19966 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19980 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19980
                                  then
                                    let uu____19981 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19981 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20028)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20059)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20090 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20104 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20104
                                     then
                                       match args with
                                       | (t,uu____20106)::[] ->
                                           let uu____20123 =
                                             let uu____20124 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20124.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20123 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20127::[],body,uu____20129)
                                                ->
                                                let uu____20156 = simp_t body
                                                   in
                                                (match uu____20156 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20159 -> tm1)
                                            | uu____20162 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20164))::(t,uu____20166)::[]
                                           ->
                                           let uu____20205 =
                                             let uu____20206 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20206.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20205 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20209::[],body,uu____20211)
                                                ->
                                                let uu____20238 = simp_t body
                                                   in
                                                (match uu____20238 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20241 -> tm1)
                                            | uu____20244 -> tm1)
                                       | uu____20245 -> tm1
                                     else
                                       (let uu____20255 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20255
                                        then
                                          match args with
                                          | (t,uu____20257)::[] ->
                                              let uu____20274 =
                                                let uu____20275 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20275.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20274 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20278::[],body,uu____20280)
                                                   ->
                                                   let uu____20307 =
                                                     simp_t body  in
                                                   (match uu____20307 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20310 -> tm1)
                                               | uu____20313 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20315))::(t,uu____20317)::[]
                                              ->
                                              let uu____20356 =
                                                let uu____20357 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20357.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20356 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20360::[],body,uu____20362)
                                                   ->
                                                   let uu____20389 =
                                                     simp_t body  in
                                                   (match uu____20389 with
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
                                                    | uu____20392 -> tm1)
                                               | uu____20395 -> tm1)
                                          | uu____20396 -> tm1
                                        else
                                          (let uu____20406 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20406
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20407;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20408;_},uu____20409)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20426;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20427;_},uu____20428)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20445 -> tm1
                                           else
                                             (let uu____20455 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20455 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20475 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20490 = simp_t t  in
                      (match uu____20490 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20493 ->
                      let uu____20516 = is_const_match tm1  in
                      (match uu____20516 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20519 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20529  ->
               (let uu____20531 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20532 = FStar_Syntax_Print.term_to_string t  in
                let uu____20533 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20540 =
                  let uu____20541 =
                    let uu____20544 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20544
                     in
                  stack_to_string uu____20541  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20531 uu____20532 uu____20533 uu____20540);
               (let uu____20567 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20567
                then
                  let uu____20568 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20568 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20575 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20576 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20577 =
                          let uu____20578 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20578
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20575
                          uu____20576 uu____20577);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20596 =
                     let uu____20597 =
                       let uu____20598 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20598  in
                     FStar_Util.string_of_int uu____20597  in
                   let uu____20603 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20604 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20596 uu____20603 uu____20604)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20610,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20659  ->
                     let uu____20660 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20660);
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
               let uu____20696 =
                 let uu___182_20697 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_20697.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_20697.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20696
           | (Arg (Univ uu____20698,uu____20699,uu____20700))::uu____20701 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20704,uu____20705))::uu____20706 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20721,uu____20722),aq,r))::stack1
               when
               let uu____20772 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20772 ->
               let t2 =
                 let uu____20776 =
                   let uu____20777 =
                     let uu____20778 = closure_as_term cfg env_arg tm  in
                     (uu____20778, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20777  in
                 uu____20776 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20784),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20837  ->
                     let uu____20838 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20838);
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
                  (let uu____20848 = FStar_ST.op_Bang m  in
                   match uu____20848 with
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
                   | FStar_Pervasives_Native.Some (uu____20985,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21032 =
                 log cfg
                   (fun uu____21036  ->
                      let uu____21037 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21037);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21041 =
                 let uu____21042 = FStar_Syntax_Subst.compress t1  in
                 uu____21042.FStar_Syntax_Syntax.n  in
               (match uu____21041 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21069 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21069  in
                    (log cfg
                       (fun uu____21073  ->
                          let uu____21074 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21074);
                     (let uu____21075 = FStar_List.tl stack  in
                      norm cfg env1 uu____21075 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21076);
                       FStar_Syntax_Syntax.pos = uu____21077;
                       FStar_Syntax_Syntax.vars = uu____21078;_},(e,uu____21080)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21109 when
                    (cfg.steps).primops ->
                    let uu____21124 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21124 with
                     | (hd1,args) ->
                         let uu____21161 =
                           let uu____21162 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21162.FStar_Syntax_Syntax.n  in
                         (match uu____21161 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21166 = find_prim_step cfg fv  in
                              (match uu____21166 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21169; arity = uu____21170;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21172;
                                     requires_binder_substitution =
                                       uu____21173;
                                     interpretation = uu____21174;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21187 -> fallback " (3)" ())
                          | uu____21190 -> fallback " (4)" ()))
                | uu____21191 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____21212  ->
                     let uu____21213 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21213);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21220 =
                   log cfg1
                     (fun uu____21225  ->
                        let uu____21226 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21227 =
                          let uu____21228 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21245  ->
                                    match uu____21245 with
                                    | (p,uu____21255,uu____21256) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21228
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21226 uu____21227);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_21273  ->
                                match uu___91_21273 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21274 -> false))
                         in
                      let steps =
                        let uu___183_21276 = cfg1.steps  in
                        {
                          beta = (uu___183_21276.beta);
                          iota = (uu___183_21276.iota);
                          zeta = false;
                          weak = (uu___183_21276.weak);
                          hnf = (uu___183_21276.hnf);
                          primops = (uu___183_21276.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_21276.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_21276.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_21276.pure_subterms_within_computations);
                          simplify = (uu___183_21276.simplify);
                          erase_universes = (uu___183_21276.erase_universes);
                          allow_unbound_universes =
                            (uu___183_21276.allow_unbound_universes);
                          reify_ = (uu___183_21276.reify_);
                          compress_uvars = (uu___183_21276.compress_uvars);
                          no_full_norm = (uu___183_21276.no_full_norm);
                          check_no_uvars = (uu___183_21276.check_no_uvars);
                          unmeta = (uu___183_21276.unmeta);
                          unascribe = (uu___183_21276.unascribe);
                          in_full_norm_request =
                            (uu___183_21276.in_full_norm_request)
                        }  in
                      let uu___184_21281 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_21281.tcenv);
                        debug = (uu___184_21281.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_21281.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_21281.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_21281.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21313 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21334 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21394  ->
                                    fun uu____21395  ->
                                      match (uu____21394, uu____21395) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21486 = norm_pat env3 p1
                                             in
                                          (match uu____21486 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21334 with
                           | (pats1,env3) ->
                               ((let uu___185_21568 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_21568.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_21587 = x  in
                            let uu____21588 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_21587.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_21587.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21588
                            }  in
                          ((let uu___187_21602 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_21602.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_21613 = x  in
                            let uu____21614 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_21613.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_21613.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21614
                            }  in
                          ((let uu___189_21628 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_21628.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_21644 = x  in
                            let uu____21645 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_21644.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_21644.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21645
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_21652 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_21652.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21662 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21676 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21676 with
                                  | (p,wopt,e) ->
                                      let uu____21696 = norm_pat env1 p  in
                                      (match uu____21696 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21721 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21721
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      if (cfg1.steps).iota
                      then norm cfg1 scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____21729 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____21729)
                    in
                 let rec is_cons head1 =
                   let uu____21734 =
                     let uu____21735 = FStar_Syntax_Subst.compress head1  in
                     uu____21735.FStar_Syntax_Syntax.n  in
                   match uu____21734 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21739) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21744 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21745;
                         FStar_Syntax_Syntax.fv_delta = uu____21746;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21747;
                         FStar_Syntax_Syntax.fv_delta = uu____21748;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21749);_}
                       -> true
                   | uu____21756 -> false  in
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
                   let uu____21901 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21901 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21988 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22027 ->
                                 let uu____22028 =
                                   let uu____22029 = is_cons head1  in
                                   Prims.op_Negation uu____22029  in
                                 FStar_Util.Inr uu____22028)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22054 =
                              let uu____22055 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22055.FStar_Syntax_Syntax.n  in
                            (match uu____22054 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22073 ->
                                 let uu____22074 =
                                   let uu____22075 = is_cons head1  in
                                   Prims.op_Negation uu____22075  in
                                 FStar_Util.Inr uu____22074))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22144)::rest_a,(p1,uu____22147)::rest_p) ->
                       let uu____22191 = matches_pat t2 p1  in
                       (match uu____22191 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22240 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22346 = matches_pat scrutinee1 p1  in
                       (match uu____22346 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____22386  ->
                                  let uu____22387 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22388 =
                                    let uu____22389 =
                                      FStar_List.map
                                        (fun uu____22399  ->
                                           match uu____22399 with
                                           | (uu____22404,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22389
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22387 uu____22388);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22436  ->
                                       match uu____22436 with
                                       | (bv,t2) ->
                                           let uu____22459 =
                                             let uu____22466 =
                                               let uu____22469 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22469
                                                in
                                             let uu____22470 =
                                               let uu____22471 =
                                                 let uu____22502 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22502, false)
                                                  in
                                               Clos uu____22471  in
                                             (uu____22466, uu____22470)  in
                                           uu____22459 :: env2) env1 s
                                 in
                              let uu____22619 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____22619)))
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
    let uu____22642 =
      let uu____22645 = FStar_ST.op_Bang plugins  in p :: uu____22645  in
    FStar_ST.op_Colon_Equals plugins uu____22642  in
  let retrieve uu____22743 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22808  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22841  ->
                  match uu___92_22841 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22845 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22851 -> d  in
        let uu____22854 = to_fsteps s  in
        let uu____22855 =
          let uu____22856 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22857 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22858 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22859 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22860 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22856;
            primop = uu____22857;
            b380 = uu____22858;
            norm_delayed = uu____22859;
            print_normalized = uu____22860
          }  in
        let uu____22861 =
          let uu____22864 =
            let uu____22867 = retrieve_plugins ()  in
            FStar_List.append uu____22867 psteps  in
          add_steps built_in_primitive_steps uu____22864  in
        let uu____22870 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22872 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22872)
           in
        {
          steps = uu____22854;
          tcenv = e;
          debug = uu____22855;
          delta_level = d1;
          primitive_steps = uu____22861;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22870
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
      fun t  -> let uu____22930 = config s e  in norm_comp uu____22930 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22943 = config [] env  in norm_universe uu____22943 [] u
  
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
        let uu____22961 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22961  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22968 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___192_22987 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___192_22987.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___192_22987.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22994 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22994
          then
            let ct1 =
              let uu____22996 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22996 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23003 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23003
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___193_23007 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___193_23007.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___193_23007.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___193_23007.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___194_23009 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___194_23009.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___194_23009.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___194_23009.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___194_23009.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___195_23010 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___195_23010.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_23010.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23012 -> c
  
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
        let uu____23024 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23024  in
      let uu____23031 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23031
      then
        let uu____23032 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23032 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23038  ->
                 let uu____23039 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23039)
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
            ((let uu____23056 =
                let uu____23061 =
                  let uu____23062 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23062
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23061)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23056);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23073 = config [AllowUnboundUniverses] env  in
          norm_comp uu____23073 [] c
        with
        | e ->
            ((let uu____23086 =
                let uu____23091 =
                  let uu____23092 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23092
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23091)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23086);
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
                   let uu____23129 =
                     let uu____23130 =
                       let uu____23137 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____23137)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23130  in
                   mk uu____23129 t01.FStar_Syntax_Syntax.pos
               | uu____23142 -> t2)
          | uu____23143 -> t2  in
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
        let uu____23183 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23183 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23212 ->
                 let uu____23219 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23219 with
                  | (actuals,uu____23229,uu____23230) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23244 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23244 with
                         | (binders,args) ->
                             let uu____23261 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23261
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
      | uu____23269 ->
          let uu____23270 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23270 with
           | (head1,args) ->
               let uu____23307 =
                 let uu____23308 = FStar_Syntax_Subst.compress head1  in
                 uu____23308.FStar_Syntax_Syntax.n  in
               (match uu____23307 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23311,thead) ->
                    let uu____23337 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23337 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23379 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_23387 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_23387.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_23387.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_23387.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_23387.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_23387.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_23387.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_23387.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_23387.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_23387.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_23387.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_23387.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_23387.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_23387.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_23387.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_23387.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_23387.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_23387.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_23387.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___200_23387.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___200_23387.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___200_23387.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_23387.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_23387.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___200_23387.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___200_23387.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___200_23387.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___200_23387.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___200_23387.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___200_23387.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___200_23387.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___200_23387.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___200_23387.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___200_23387.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23379 with
                            | (uu____23388,ty,uu____23390) ->
                                eta_expand_with_type env t ty))
                | uu____23391 ->
                    let uu____23392 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_23400 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_23400.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_23400.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_23400.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_23400.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_23400.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_23400.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_23400.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_23400.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_23400.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_23400.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_23400.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_23400.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_23400.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_23400.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_23400.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_23400.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_23400.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_23400.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___201_23400.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___201_23400.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___201_23400.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_23400.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_23400.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___201_23400.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___201_23400.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___201_23400.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___201_23400.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___201_23400.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___201_23400.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___201_23400.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___201_23400.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___201_23400.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___201_23400.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23392 with
                     | (uu____23401,ty,uu____23403) ->
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
      let uu___202_23460 = x  in
      let uu____23461 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___202_23460.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___202_23460.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23461
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23464 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23489 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23490 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23491 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23492 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23499 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23500 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23501 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___203_23529 = rc  in
          let uu____23530 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23537 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___203_23529.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23530;
            FStar_Syntax_Syntax.residual_flags = uu____23537
          }  in
        let uu____23540 =
          let uu____23541 =
            let uu____23558 = elim_delayed_subst_binders bs  in
            let uu____23565 = elim_delayed_subst_term t2  in
            let uu____23566 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23558, uu____23565, uu____23566)  in
          FStar_Syntax_Syntax.Tm_abs uu____23541  in
        mk1 uu____23540
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23595 =
          let uu____23596 =
            let uu____23609 = elim_delayed_subst_binders bs  in
            let uu____23616 = elim_delayed_subst_comp c  in
            (uu____23609, uu____23616)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23596  in
        mk1 uu____23595
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23629 =
          let uu____23630 =
            let uu____23637 = elim_bv bv  in
            let uu____23638 = elim_delayed_subst_term phi  in
            (uu____23637, uu____23638)  in
          FStar_Syntax_Syntax.Tm_refine uu____23630  in
        mk1 uu____23629
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____23661 =
          let uu____23662 =
            let uu____23677 = elim_delayed_subst_term t2  in
            let uu____23678 = elim_delayed_subst_args args  in
            (uu____23677, uu____23678)  in
          FStar_Syntax_Syntax.Tm_app uu____23662  in
        mk1 uu____23661
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___204_23742 = p  in
              let uu____23743 =
                let uu____23744 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23744  in
              {
                FStar_Syntax_Syntax.v = uu____23743;
                FStar_Syntax_Syntax.p =
                  (uu___204_23742.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___205_23746 = p  in
              let uu____23747 =
                let uu____23748 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23748  in
              {
                FStar_Syntax_Syntax.v = uu____23747;
                FStar_Syntax_Syntax.p =
                  (uu___205_23746.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___206_23755 = p  in
              let uu____23756 =
                let uu____23757 =
                  let uu____23764 = elim_bv x  in
                  let uu____23765 = elim_delayed_subst_term t0  in
                  (uu____23764, uu____23765)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23757  in
              {
                FStar_Syntax_Syntax.v = uu____23756;
                FStar_Syntax_Syntax.p =
                  (uu___206_23755.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___207_23784 = p  in
              let uu____23785 =
                let uu____23786 =
                  let uu____23799 =
                    FStar_List.map
                      (fun uu____23822  ->
                         match uu____23822 with
                         | (x,b) ->
                             let uu____23835 = elim_pat x  in
                             (uu____23835, b)) pats
                     in
                  (fv, uu____23799)  in
                FStar_Syntax_Syntax.Pat_cons uu____23786  in
              {
                FStar_Syntax_Syntax.v = uu____23785;
                FStar_Syntax_Syntax.p =
                  (uu___207_23784.FStar_Syntax_Syntax.p)
              }
          | uu____23848 -> p  in
        let elim_branch uu____23870 =
          match uu____23870 with
          | (pat,wopt,t3) ->
              let uu____23896 = elim_pat pat  in
              let uu____23899 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23902 = elim_delayed_subst_term t3  in
              (uu____23896, uu____23899, uu____23902)
           in
        let uu____23907 =
          let uu____23908 =
            let uu____23931 = elim_delayed_subst_term t2  in
            let uu____23932 = FStar_List.map elim_branch branches  in
            (uu____23931, uu____23932)  in
          FStar_Syntax_Syntax.Tm_match uu____23908  in
        mk1 uu____23907
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24041 =
          match uu____24041 with
          | (tc,topt) ->
              let uu____24076 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24086 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24086
                | FStar_Util.Inr c ->
                    let uu____24088 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24088
                 in
              let uu____24089 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24076, uu____24089)
           in
        let uu____24098 =
          let uu____24099 =
            let uu____24126 = elim_delayed_subst_term t2  in
            let uu____24127 = elim_ascription a  in
            (uu____24126, uu____24127, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24099  in
        mk1 uu____24098
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___208_24172 = lb  in
          let uu____24173 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24176 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___208_24172.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___208_24172.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24173;
            FStar_Syntax_Syntax.lbeff =
              (uu___208_24172.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24176;
            FStar_Syntax_Syntax.lbattrs =
              (uu___208_24172.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___208_24172.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24179 =
          let uu____24180 =
            let uu____24193 =
              let uu____24200 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24200)  in
            let uu____24209 = elim_delayed_subst_term t2  in
            (uu____24193, uu____24209)  in
          FStar_Syntax_Syntax.Tm_let uu____24180  in
        mk1 uu____24179
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24242 =
          let uu____24243 =
            let uu____24260 = elim_delayed_subst_term t2  in
            (uv, uu____24260)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24243  in
        mk1 uu____24242
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24278 =
          let uu____24279 =
            let uu____24286 = elim_delayed_subst_term tm  in
            (uu____24286, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24279  in
        mk1 uu____24278
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24293 =
          let uu____24294 =
            let uu____24301 = elim_delayed_subst_term t2  in
            let uu____24302 = elim_delayed_subst_meta md  in
            (uu____24301, uu____24302)  in
          FStar_Syntax_Syntax.Tm_meta uu____24294  in
        mk1 uu____24293

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24309  ->
         match uu___93_24309 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24313 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24313
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
        let uu____24334 =
          let uu____24335 =
            let uu____24344 = elim_delayed_subst_term t  in
            (uu____24344, uopt)  in
          FStar_Syntax_Syntax.Total uu____24335  in
        mk1 uu____24334
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24357 =
          let uu____24358 =
            let uu____24367 = elim_delayed_subst_term t  in
            (uu____24367, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24358  in
        mk1 uu____24357
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___209_24372 = ct  in
          let uu____24373 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24376 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24385 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___209_24372.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___209_24372.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24373;
            FStar_Syntax_Syntax.effect_args = uu____24376;
            FStar_Syntax_Syntax.flags = uu____24385
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24388  ->
    match uu___94_24388 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24400 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24400
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24433 =
          let uu____24440 = elim_delayed_subst_term t  in (m, uu____24440)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24433
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24448 =
          let uu____24457 = elim_delayed_subst_term t  in
          (m1, m2, uu____24457)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24448
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24480  ->
         match uu____24480 with
         | (t,q) ->
             let uu____24491 = elim_delayed_subst_term t  in (uu____24491, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24511  ->
         match uu____24511 with
         | (x,q) ->
             let uu____24522 =
               let uu___210_24523 = x  in
               let uu____24524 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___210_24523.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___210_24523.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24524
               }  in
             (uu____24522, q)) bs

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
            | (uu____24600,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24606,FStar_Util.Inl t) ->
                let uu____24612 =
                  let uu____24615 =
                    let uu____24616 =
                      let uu____24629 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____24629)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____24616  in
                  FStar_Syntax_Syntax.mk uu____24615  in
                uu____24612 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____24633 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____24633 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____24661 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24716 ->
                    let uu____24717 =
                      let uu____24726 =
                        let uu____24727 = FStar_Syntax_Subst.compress t4  in
                        uu____24727.FStar_Syntax_Syntax.n  in
                      (uu____24726, tc)  in
                    (match uu____24717 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24752) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24789) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24828,FStar_Util.Inl uu____24829) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24852 -> failwith "Impossible")
                 in
              (match uu____24661 with
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
          let uu____24957 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24957 with
          | (univ_names1,binders1,tc) ->
              let uu____25015 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25015)
  
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
          let uu____25050 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25050 with
          | (univ_names1,binders1,tc) ->
              let uu____25110 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25110)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25143 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25143 with
           | (univ_names1,binders1,typ1) ->
               let uu___211_25171 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_25171.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_25171.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_25171.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_25171.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___212_25192 = s  in
          let uu____25193 =
            let uu____25194 =
              let uu____25203 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25203, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25194  in
          {
            FStar_Syntax_Syntax.sigel = uu____25193;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_25192.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_25192.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_25192.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_25192.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25220 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25220 with
           | (univ_names1,uu____25238,typ1) ->
               let uu___213_25252 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_25252.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_25252.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_25252.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_25252.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25258 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25258 with
           | (univ_names1,uu____25276,typ1) ->
               let uu___214_25290 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_25290.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_25290.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_25290.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_25290.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25324 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25324 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25347 =
                            let uu____25348 =
                              let uu____25349 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25349  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25348
                             in
                          elim_delayed_subst_term uu____25347  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___215_25352 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___215_25352.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_25352.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___215_25352.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___215_25352.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___216_25353 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___216_25353.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_25353.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_25353.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_25353.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___217_25365 = s  in
          let uu____25366 =
            let uu____25367 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25367  in
          {
            FStar_Syntax_Syntax.sigel = uu____25366;
            FStar_Syntax_Syntax.sigrng =
              (uu___217_25365.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_25365.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_25365.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_25365.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25371 = elim_uvars_aux_t env us [] t  in
          (match uu____25371 with
           | (us1,uu____25389,t1) ->
               let uu___218_25403 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_25403.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_25403.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_25403.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_25403.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25404 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25406 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25406 with
           | (univs1,binders,signature) ->
               let uu____25434 =
                 let uu____25443 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____25443 with
                 | (univs_opening,univs2) ->
                     let uu____25470 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25470)
                  in
               (match uu____25434 with
                | (univs_opening,univs_closing) ->
                    let uu____25487 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25493 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25494 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25493, uu____25494)  in
                    (match uu____25487 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____25516 =
                           match uu____25516 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____25534 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____25534 with
                                | (us1,t1) ->
                                    let uu____25545 =
                                      let uu____25550 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____25557 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____25550, uu____25557)  in
                                    (match uu____25545 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____25570 =
                                           let uu____25575 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____25584 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____25575, uu____25584)  in
                                         (match uu____25570 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25600 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25600
                                                 in
                                              let uu____25601 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____25601 with
                                               | (uu____25622,uu____25623,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____25638 =
                                                       let uu____25639 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25639
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25638
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____25644 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____25644 with
                           | (uu____25657,uu____25658,t1) -> t1  in
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
                             | uu____25718 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25735 =
                               let uu____25736 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25736.FStar_Syntax_Syntax.n  in
                             match uu____25735 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25795 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25824 =
                               let uu____25825 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25825.FStar_Syntax_Syntax.n  in
                             match uu____25824 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25846) ->
                                 let uu____25867 = destruct_action_body body
                                    in
                                 (match uu____25867 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25912 ->
                                 let uu____25913 = destruct_action_body t  in
                                 (match uu____25913 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25962 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25962 with
                           | (action_univs,t) ->
                               let uu____25971 = destruct_action_typ_templ t
                                  in
                               (match uu____25971 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___219_26012 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___219_26012.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___219_26012.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___220_26014 = ed  in
                           let uu____26015 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26016 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26017 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26018 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26019 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26020 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26021 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26022 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26023 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26024 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26025 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26026 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26027 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26028 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___220_26014.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___220_26014.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26015;
                             FStar_Syntax_Syntax.bind_wp = uu____26016;
                             FStar_Syntax_Syntax.if_then_else = uu____26017;
                             FStar_Syntax_Syntax.ite_wp = uu____26018;
                             FStar_Syntax_Syntax.stronger = uu____26019;
                             FStar_Syntax_Syntax.close_wp = uu____26020;
                             FStar_Syntax_Syntax.assert_p = uu____26021;
                             FStar_Syntax_Syntax.assume_p = uu____26022;
                             FStar_Syntax_Syntax.null_wp = uu____26023;
                             FStar_Syntax_Syntax.trivial = uu____26024;
                             FStar_Syntax_Syntax.repr = uu____26025;
                             FStar_Syntax_Syntax.return_repr = uu____26026;
                             FStar_Syntax_Syntax.bind_repr = uu____26027;
                             FStar_Syntax_Syntax.actions = uu____26028;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___220_26014.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___221_26031 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___221_26031.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___221_26031.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___221_26031.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___221_26031.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_26048 =
            match uu___95_26048 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26075 = elim_uvars_aux_t env us [] t  in
                (match uu____26075 with
                 | (us1,uu____26099,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___222_26118 = sub_eff  in
            let uu____26119 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26122 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___222_26118.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___222_26118.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26119;
              FStar_Syntax_Syntax.lift = uu____26122
            }  in
          let uu___223_26125 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___223_26125.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_26125.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_26125.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_26125.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26135 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26135 with
           | (univ_names1,binders1,comp1) ->
               let uu___224_26169 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_26169.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_26169.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_26169.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_26169.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26180 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26181 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  