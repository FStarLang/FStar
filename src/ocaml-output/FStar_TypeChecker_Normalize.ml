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
  in_full_norm_request: Prims.bool ;
  weakly_reduce_scrutinee: Prims.bool }[@@deriving show]
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__in_full_norm_request
  
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
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
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__weakly_reduce_scrutinee
  
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
    in_full_norm_request = false;
    weakly_reduce_scrutinee = true
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___78_1360 =
        match uu___78_1360 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1380 = fs  in
          {
            beta = true;
            iota = (uu___96_1380.iota);
            zeta = (uu___96_1380.zeta);
            weak = (uu___96_1380.weak);
            hnf = (uu___96_1380.hnf);
            primops = (uu___96_1380.primops);
            do_not_unfold_pure_lets = (uu___96_1380.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1380.unfold_until);
            unfold_only = (uu___96_1380.unfold_only);
            unfold_fully = (uu___96_1380.unfold_fully);
            unfold_attr = (uu___96_1380.unfold_attr);
            unfold_tac = (uu___96_1380.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1380.pure_subterms_within_computations);
            simplify = (uu___96_1380.simplify);
            erase_universes = (uu___96_1380.erase_universes);
            allow_unbound_universes = (uu___96_1380.allow_unbound_universes);
            reify_ = (uu___96_1380.reify_);
            compress_uvars = (uu___96_1380.compress_uvars);
            no_full_norm = (uu___96_1380.no_full_norm);
            check_no_uvars = (uu___96_1380.check_no_uvars);
            unmeta = (uu___96_1380.unmeta);
            unascribe = (uu___96_1380.unascribe);
            in_full_norm_request = (uu___96_1380.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___96_1380.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___97_1381 = fs  in
          {
            beta = (uu___97_1381.beta);
            iota = true;
            zeta = (uu___97_1381.zeta);
            weak = (uu___97_1381.weak);
            hnf = (uu___97_1381.hnf);
            primops = (uu___97_1381.primops);
            do_not_unfold_pure_lets = (uu___97_1381.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1381.unfold_until);
            unfold_only = (uu___97_1381.unfold_only);
            unfold_fully = (uu___97_1381.unfold_fully);
            unfold_attr = (uu___97_1381.unfold_attr);
            unfold_tac = (uu___97_1381.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1381.pure_subterms_within_computations);
            simplify = (uu___97_1381.simplify);
            erase_universes = (uu___97_1381.erase_universes);
            allow_unbound_universes = (uu___97_1381.allow_unbound_universes);
            reify_ = (uu___97_1381.reify_);
            compress_uvars = (uu___97_1381.compress_uvars);
            no_full_norm = (uu___97_1381.no_full_norm);
            check_no_uvars = (uu___97_1381.check_no_uvars);
            unmeta = (uu___97_1381.unmeta);
            unascribe = (uu___97_1381.unascribe);
            in_full_norm_request = (uu___97_1381.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_1381.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___98_1382 = fs  in
          {
            beta = (uu___98_1382.beta);
            iota = (uu___98_1382.iota);
            zeta = true;
            weak = (uu___98_1382.weak);
            hnf = (uu___98_1382.hnf);
            primops = (uu___98_1382.primops);
            do_not_unfold_pure_lets = (uu___98_1382.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1382.unfold_until);
            unfold_only = (uu___98_1382.unfold_only);
            unfold_fully = (uu___98_1382.unfold_fully);
            unfold_attr = (uu___98_1382.unfold_attr);
            unfold_tac = (uu___98_1382.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1382.pure_subterms_within_computations);
            simplify = (uu___98_1382.simplify);
            erase_universes = (uu___98_1382.erase_universes);
            allow_unbound_universes = (uu___98_1382.allow_unbound_universes);
            reify_ = (uu___98_1382.reify_);
            compress_uvars = (uu___98_1382.compress_uvars);
            no_full_norm = (uu___98_1382.no_full_norm);
            check_no_uvars = (uu___98_1382.check_no_uvars);
            unmeta = (uu___98_1382.unmeta);
            unascribe = (uu___98_1382.unascribe);
            in_full_norm_request = (uu___98_1382.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___98_1382.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___99_1383 = fs  in
          {
            beta = false;
            iota = (uu___99_1383.iota);
            zeta = (uu___99_1383.zeta);
            weak = (uu___99_1383.weak);
            hnf = (uu___99_1383.hnf);
            primops = (uu___99_1383.primops);
            do_not_unfold_pure_lets = (uu___99_1383.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1383.unfold_until);
            unfold_only = (uu___99_1383.unfold_only);
            unfold_fully = (uu___99_1383.unfold_fully);
            unfold_attr = (uu___99_1383.unfold_attr);
            unfold_tac = (uu___99_1383.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1383.pure_subterms_within_computations);
            simplify = (uu___99_1383.simplify);
            erase_universes = (uu___99_1383.erase_universes);
            allow_unbound_universes = (uu___99_1383.allow_unbound_universes);
            reify_ = (uu___99_1383.reify_);
            compress_uvars = (uu___99_1383.compress_uvars);
            no_full_norm = (uu___99_1383.no_full_norm);
            check_no_uvars = (uu___99_1383.check_no_uvars);
            unmeta = (uu___99_1383.unmeta);
            unascribe = (uu___99_1383.unascribe);
            in_full_norm_request = (uu___99_1383.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___99_1383.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___100_1384 = fs  in
          {
            beta = (uu___100_1384.beta);
            iota = false;
            zeta = (uu___100_1384.zeta);
            weak = (uu___100_1384.weak);
            hnf = (uu___100_1384.hnf);
            primops = (uu___100_1384.primops);
            do_not_unfold_pure_lets = (uu___100_1384.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1384.unfold_until);
            unfold_only = (uu___100_1384.unfold_only);
            unfold_fully = (uu___100_1384.unfold_fully);
            unfold_attr = (uu___100_1384.unfold_attr);
            unfold_tac = (uu___100_1384.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1384.pure_subterms_within_computations);
            simplify = (uu___100_1384.simplify);
            erase_universes = (uu___100_1384.erase_universes);
            allow_unbound_universes = (uu___100_1384.allow_unbound_universes);
            reify_ = (uu___100_1384.reify_);
            compress_uvars = (uu___100_1384.compress_uvars);
            no_full_norm = (uu___100_1384.no_full_norm);
            check_no_uvars = (uu___100_1384.check_no_uvars);
            unmeta = (uu___100_1384.unmeta);
            unascribe = (uu___100_1384.unascribe);
            in_full_norm_request = (uu___100_1384.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_1384.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___101_1385 = fs  in
          {
            beta = (uu___101_1385.beta);
            iota = (uu___101_1385.iota);
            zeta = false;
            weak = (uu___101_1385.weak);
            hnf = (uu___101_1385.hnf);
            primops = (uu___101_1385.primops);
            do_not_unfold_pure_lets = (uu___101_1385.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1385.unfold_until);
            unfold_only = (uu___101_1385.unfold_only);
            unfold_fully = (uu___101_1385.unfold_fully);
            unfold_attr = (uu___101_1385.unfold_attr);
            unfold_tac = (uu___101_1385.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1385.pure_subterms_within_computations);
            simplify = (uu___101_1385.simplify);
            erase_universes = (uu___101_1385.erase_universes);
            allow_unbound_universes = (uu___101_1385.allow_unbound_universes);
            reify_ = (uu___101_1385.reify_);
            compress_uvars = (uu___101_1385.compress_uvars);
            no_full_norm = (uu___101_1385.no_full_norm);
            check_no_uvars = (uu___101_1385.check_no_uvars);
            unmeta = (uu___101_1385.unmeta);
            unascribe = (uu___101_1385.unascribe);
            in_full_norm_request = (uu___101_1385.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___101_1385.weakly_reduce_scrutinee)
          }
      | Exclude uu____1386 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1387 = fs  in
          {
            beta = (uu___102_1387.beta);
            iota = (uu___102_1387.iota);
            zeta = (uu___102_1387.zeta);
            weak = true;
            hnf = (uu___102_1387.hnf);
            primops = (uu___102_1387.primops);
            do_not_unfold_pure_lets = (uu___102_1387.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1387.unfold_until);
            unfold_only = (uu___102_1387.unfold_only);
            unfold_fully = (uu___102_1387.unfold_fully);
            unfold_attr = (uu___102_1387.unfold_attr);
            unfold_tac = (uu___102_1387.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1387.pure_subterms_within_computations);
            simplify = (uu___102_1387.simplify);
            erase_universes = (uu___102_1387.erase_universes);
            allow_unbound_universes = (uu___102_1387.allow_unbound_universes);
            reify_ = (uu___102_1387.reify_);
            compress_uvars = (uu___102_1387.compress_uvars);
            no_full_norm = (uu___102_1387.no_full_norm);
            check_no_uvars = (uu___102_1387.check_no_uvars);
            unmeta = (uu___102_1387.unmeta);
            unascribe = (uu___102_1387.unascribe);
            in_full_norm_request = (uu___102_1387.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___102_1387.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___103_1388 = fs  in
          {
            beta = (uu___103_1388.beta);
            iota = (uu___103_1388.iota);
            zeta = (uu___103_1388.zeta);
            weak = (uu___103_1388.weak);
            hnf = true;
            primops = (uu___103_1388.primops);
            do_not_unfold_pure_lets = (uu___103_1388.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1388.unfold_until);
            unfold_only = (uu___103_1388.unfold_only);
            unfold_fully = (uu___103_1388.unfold_fully);
            unfold_attr = (uu___103_1388.unfold_attr);
            unfold_tac = (uu___103_1388.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1388.pure_subterms_within_computations);
            simplify = (uu___103_1388.simplify);
            erase_universes = (uu___103_1388.erase_universes);
            allow_unbound_universes = (uu___103_1388.allow_unbound_universes);
            reify_ = (uu___103_1388.reify_);
            compress_uvars = (uu___103_1388.compress_uvars);
            no_full_norm = (uu___103_1388.no_full_norm);
            check_no_uvars = (uu___103_1388.check_no_uvars);
            unmeta = (uu___103_1388.unmeta);
            unascribe = (uu___103_1388.unascribe);
            in_full_norm_request = (uu___103_1388.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_1388.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___104_1389 = fs  in
          {
            beta = (uu___104_1389.beta);
            iota = (uu___104_1389.iota);
            zeta = (uu___104_1389.zeta);
            weak = (uu___104_1389.weak);
            hnf = (uu___104_1389.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1389.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1389.unfold_until);
            unfold_only = (uu___104_1389.unfold_only);
            unfold_fully = (uu___104_1389.unfold_fully);
            unfold_attr = (uu___104_1389.unfold_attr);
            unfold_tac = (uu___104_1389.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1389.pure_subterms_within_computations);
            simplify = (uu___104_1389.simplify);
            erase_universes = (uu___104_1389.erase_universes);
            allow_unbound_universes = (uu___104_1389.allow_unbound_universes);
            reify_ = (uu___104_1389.reify_);
            compress_uvars = (uu___104_1389.compress_uvars);
            no_full_norm = (uu___104_1389.no_full_norm);
            check_no_uvars = (uu___104_1389.check_no_uvars);
            unmeta = (uu___104_1389.unmeta);
            unascribe = (uu___104_1389.unascribe);
            in_full_norm_request = (uu___104_1389.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_1389.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1390 = fs  in
          {
            beta = (uu___105_1390.beta);
            iota = (uu___105_1390.iota);
            zeta = (uu___105_1390.zeta);
            weak = (uu___105_1390.weak);
            hnf = (uu___105_1390.hnf);
            primops = (uu___105_1390.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1390.unfold_until);
            unfold_only = (uu___105_1390.unfold_only);
            unfold_fully = (uu___105_1390.unfold_fully);
            unfold_attr = (uu___105_1390.unfold_attr);
            unfold_tac = (uu___105_1390.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1390.pure_subterms_within_computations);
            simplify = (uu___105_1390.simplify);
            erase_universes = (uu___105_1390.erase_universes);
            allow_unbound_universes = (uu___105_1390.allow_unbound_universes);
            reify_ = (uu___105_1390.reify_);
            compress_uvars = (uu___105_1390.compress_uvars);
            no_full_norm = (uu___105_1390.no_full_norm);
            check_no_uvars = (uu___105_1390.check_no_uvars);
            unmeta = (uu___105_1390.unmeta);
            unascribe = (uu___105_1390.unascribe);
            in_full_norm_request = (uu___105_1390.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___105_1390.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___106_1392 = fs  in
          {
            beta = (uu___106_1392.beta);
            iota = (uu___106_1392.iota);
            zeta = (uu___106_1392.zeta);
            weak = (uu___106_1392.weak);
            hnf = (uu___106_1392.hnf);
            primops = (uu___106_1392.primops);
            do_not_unfold_pure_lets = (uu___106_1392.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1392.unfold_only);
            unfold_fully = (uu___106_1392.unfold_fully);
            unfold_attr = (uu___106_1392.unfold_attr);
            unfold_tac = (uu___106_1392.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1392.pure_subterms_within_computations);
            simplify = (uu___106_1392.simplify);
            erase_universes = (uu___106_1392.erase_universes);
            allow_unbound_universes = (uu___106_1392.allow_unbound_universes);
            reify_ = (uu___106_1392.reify_);
            compress_uvars = (uu___106_1392.compress_uvars);
            no_full_norm = (uu___106_1392.no_full_norm);
            check_no_uvars = (uu___106_1392.check_no_uvars);
            unmeta = (uu___106_1392.unmeta);
            unascribe = (uu___106_1392.unascribe);
            in_full_norm_request = (uu___106_1392.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_1392.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___107_1396 = fs  in
          {
            beta = (uu___107_1396.beta);
            iota = (uu___107_1396.iota);
            zeta = (uu___107_1396.zeta);
            weak = (uu___107_1396.weak);
            hnf = (uu___107_1396.hnf);
            primops = (uu___107_1396.primops);
            do_not_unfold_pure_lets = (uu___107_1396.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1396.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1396.unfold_fully);
            unfold_attr = (uu___107_1396.unfold_attr);
            unfold_tac = (uu___107_1396.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1396.pure_subterms_within_computations);
            simplify = (uu___107_1396.simplify);
            erase_universes = (uu___107_1396.erase_universes);
            allow_unbound_universes = (uu___107_1396.allow_unbound_universes);
            reify_ = (uu___107_1396.reify_);
            compress_uvars = (uu___107_1396.compress_uvars);
            no_full_norm = (uu___107_1396.no_full_norm);
            check_no_uvars = (uu___107_1396.check_no_uvars);
            unmeta = (uu___107_1396.unmeta);
            unascribe = (uu___107_1396.unascribe);
            in_full_norm_request = (uu___107_1396.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___107_1396.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___108_1402 = fs  in
          {
            beta = (uu___108_1402.beta);
            iota = (uu___108_1402.iota);
            zeta = (uu___108_1402.zeta);
            weak = (uu___108_1402.weak);
            hnf = (uu___108_1402.hnf);
            primops = (uu___108_1402.primops);
            do_not_unfold_pure_lets = (uu___108_1402.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1402.unfold_until);
            unfold_only = (uu___108_1402.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1402.unfold_attr);
            unfold_tac = (uu___108_1402.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1402.pure_subterms_within_computations);
            simplify = (uu___108_1402.simplify);
            erase_universes = (uu___108_1402.erase_universes);
            allow_unbound_universes = (uu___108_1402.allow_unbound_universes);
            reify_ = (uu___108_1402.reify_);
            compress_uvars = (uu___108_1402.compress_uvars);
            no_full_norm = (uu___108_1402.no_full_norm);
            check_no_uvars = (uu___108_1402.check_no_uvars);
            unmeta = (uu___108_1402.unmeta);
            unascribe = (uu___108_1402.unascribe);
            in_full_norm_request = (uu___108_1402.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_1402.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___109_1406 = fs  in
          {
            beta = (uu___109_1406.beta);
            iota = (uu___109_1406.iota);
            zeta = (uu___109_1406.zeta);
            weak = (uu___109_1406.weak);
            hnf = (uu___109_1406.hnf);
            primops = (uu___109_1406.primops);
            do_not_unfold_pure_lets = (uu___109_1406.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1406.unfold_until);
            unfold_only = (uu___109_1406.unfold_only);
            unfold_fully = (uu___109_1406.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1406.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1406.pure_subterms_within_computations);
            simplify = (uu___109_1406.simplify);
            erase_universes = (uu___109_1406.erase_universes);
            allow_unbound_universes = (uu___109_1406.allow_unbound_universes);
            reify_ = (uu___109_1406.reify_);
            compress_uvars = (uu___109_1406.compress_uvars);
            no_full_norm = (uu___109_1406.no_full_norm);
            check_no_uvars = (uu___109_1406.check_no_uvars);
            unmeta = (uu___109_1406.unmeta);
            unascribe = (uu___109_1406.unascribe);
            in_full_norm_request = (uu___109_1406.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___109_1406.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___110_1407 = fs  in
          {
            beta = (uu___110_1407.beta);
            iota = (uu___110_1407.iota);
            zeta = (uu___110_1407.zeta);
            weak = (uu___110_1407.weak);
            hnf = (uu___110_1407.hnf);
            primops = (uu___110_1407.primops);
            do_not_unfold_pure_lets = (uu___110_1407.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1407.unfold_until);
            unfold_only = (uu___110_1407.unfold_only);
            unfold_fully = (uu___110_1407.unfold_fully);
            unfold_attr = (uu___110_1407.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1407.pure_subterms_within_computations);
            simplify = (uu___110_1407.simplify);
            erase_universes = (uu___110_1407.erase_universes);
            allow_unbound_universes = (uu___110_1407.allow_unbound_universes);
            reify_ = (uu___110_1407.reify_);
            compress_uvars = (uu___110_1407.compress_uvars);
            no_full_norm = (uu___110_1407.no_full_norm);
            check_no_uvars = (uu___110_1407.check_no_uvars);
            unmeta = (uu___110_1407.unmeta);
            unascribe = (uu___110_1407.unascribe);
            in_full_norm_request = (uu___110_1407.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_1407.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1408 = fs  in
          {
            beta = (uu___111_1408.beta);
            iota = (uu___111_1408.iota);
            zeta = (uu___111_1408.zeta);
            weak = (uu___111_1408.weak);
            hnf = (uu___111_1408.hnf);
            primops = (uu___111_1408.primops);
            do_not_unfold_pure_lets = (uu___111_1408.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1408.unfold_until);
            unfold_only = (uu___111_1408.unfold_only);
            unfold_fully = (uu___111_1408.unfold_fully);
            unfold_attr = (uu___111_1408.unfold_attr);
            unfold_tac = (uu___111_1408.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1408.simplify);
            erase_universes = (uu___111_1408.erase_universes);
            allow_unbound_universes = (uu___111_1408.allow_unbound_universes);
            reify_ = (uu___111_1408.reify_);
            compress_uvars = (uu___111_1408.compress_uvars);
            no_full_norm = (uu___111_1408.no_full_norm);
            check_no_uvars = (uu___111_1408.check_no_uvars);
            unmeta = (uu___111_1408.unmeta);
            unascribe = (uu___111_1408.unascribe);
            in_full_norm_request = (uu___111_1408.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___111_1408.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___112_1409 = fs  in
          {
            beta = (uu___112_1409.beta);
            iota = (uu___112_1409.iota);
            zeta = (uu___112_1409.zeta);
            weak = (uu___112_1409.weak);
            hnf = (uu___112_1409.hnf);
            primops = (uu___112_1409.primops);
            do_not_unfold_pure_lets = (uu___112_1409.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1409.unfold_until);
            unfold_only = (uu___112_1409.unfold_only);
            unfold_fully = (uu___112_1409.unfold_fully);
            unfold_attr = (uu___112_1409.unfold_attr);
            unfold_tac = (uu___112_1409.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1409.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1409.erase_universes);
            allow_unbound_universes = (uu___112_1409.allow_unbound_universes);
            reify_ = (uu___112_1409.reify_);
            compress_uvars = (uu___112_1409.compress_uvars);
            no_full_norm = (uu___112_1409.no_full_norm);
            check_no_uvars = (uu___112_1409.check_no_uvars);
            unmeta = (uu___112_1409.unmeta);
            unascribe = (uu___112_1409.unascribe);
            in_full_norm_request = (uu___112_1409.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_1409.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___113_1410 = fs  in
          {
            beta = (uu___113_1410.beta);
            iota = (uu___113_1410.iota);
            zeta = (uu___113_1410.zeta);
            weak = (uu___113_1410.weak);
            hnf = (uu___113_1410.hnf);
            primops = (uu___113_1410.primops);
            do_not_unfold_pure_lets = (uu___113_1410.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1410.unfold_until);
            unfold_only = (uu___113_1410.unfold_only);
            unfold_fully = (uu___113_1410.unfold_fully);
            unfold_attr = (uu___113_1410.unfold_attr);
            unfold_tac = (uu___113_1410.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1410.pure_subterms_within_computations);
            simplify = (uu___113_1410.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1410.allow_unbound_universes);
            reify_ = (uu___113_1410.reify_);
            compress_uvars = (uu___113_1410.compress_uvars);
            no_full_norm = (uu___113_1410.no_full_norm);
            check_no_uvars = (uu___113_1410.check_no_uvars);
            unmeta = (uu___113_1410.unmeta);
            unascribe = (uu___113_1410.unascribe);
            in_full_norm_request = (uu___113_1410.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___113_1410.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1411 = fs  in
          {
            beta = (uu___114_1411.beta);
            iota = (uu___114_1411.iota);
            zeta = (uu___114_1411.zeta);
            weak = (uu___114_1411.weak);
            hnf = (uu___114_1411.hnf);
            primops = (uu___114_1411.primops);
            do_not_unfold_pure_lets = (uu___114_1411.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1411.unfold_until);
            unfold_only = (uu___114_1411.unfold_only);
            unfold_fully = (uu___114_1411.unfold_fully);
            unfold_attr = (uu___114_1411.unfold_attr);
            unfold_tac = (uu___114_1411.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1411.pure_subterms_within_computations);
            simplify = (uu___114_1411.simplify);
            erase_universes = (uu___114_1411.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1411.reify_);
            compress_uvars = (uu___114_1411.compress_uvars);
            no_full_norm = (uu___114_1411.no_full_norm);
            check_no_uvars = (uu___114_1411.check_no_uvars);
            unmeta = (uu___114_1411.unmeta);
            unascribe = (uu___114_1411.unascribe);
            in_full_norm_request = (uu___114_1411.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_1411.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___115_1412 = fs  in
          {
            beta = (uu___115_1412.beta);
            iota = (uu___115_1412.iota);
            zeta = (uu___115_1412.zeta);
            weak = (uu___115_1412.weak);
            hnf = (uu___115_1412.hnf);
            primops = (uu___115_1412.primops);
            do_not_unfold_pure_lets = (uu___115_1412.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1412.unfold_until);
            unfold_only = (uu___115_1412.unfold_only);
            unfold_fully = (uu___115_1412.unfold_fully);
            unfold_attr = (uu___115_1412.unfold_attr);
            unfold_tac = (uu___115_1412.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1412.pure_subterms_within_computations);
            simplify = (uu___115_1412.simplify);
            erase_universes = (uu___115_1412.erase_universes);
            allow_unbound_universes = (uu___115_1412.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1412.compress_uvars);
            no_full_norm = (uu___115_1412.no_full_norm);
            check_no_uvars = (uu___115_1412.check_no_uvars);
            unmeta = (uu___115_1412.unmeta);
            unascribe = (uu___115_1412.unascribe);
            in_full_norm_request = (uu___115_1412.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___115_1412.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___116_1413 = fs  in
          {
            beta = (uu___116_1413.beta);
            iota = (uu___116_1413.iota);
            zeta = (uu___116_1413.zeta);
            weak = (uu___116_1413.weak);
            hnf = (uu___116_1413.hnf);
            primops = (uu___116_1413.primops);
            do_not_unfold_pure_lets = (uu___116_1413.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1413.unfold_until);
            unfold_only = (uu___116_1413.unfold_only);
            unfold_fully = (uu___116_1413.unfold_fully);
            unfold_attr = (uu___116_1413.unfold_attr);
            unfold_tac = (uu___116_1413.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1413.pure_subterms_within_computations);
            simplify = (uu___116_1413.simplify);
            erase_universes = (uu___116_1413.erase_universes);
            allow_unbound_universes = (uu___116_1413.allow_unbound_universes);
            reify_ = (uu___116_1413.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1413.no_full_norm);
            check_no_uvars = (uu___116_1413.check_no_uvars);
            unmeta = (uu___116_1413.unmeta);
            unascribe = (uu___116_1413.unascribe);
            in_full_norm_request = (uu___116_1413.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___116_1413.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___117_1414 = fs  in
          {
            beta = (uu___117_1414.beta);
            iota = (uu___117_1414.iota);
            zeta = (uu___117_1414.zeta);
            weak = (uu___117_1414.weak);
            hnf = (uu___117_1414.hnf);
            primops = (uu___117_1414.primops);
            do_not_unfold_pure_lets = (uu___117_1414.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1414.unfold_until);
            unfold_only = (uu___117_1414.unfold_only);
            unfold_fully = (uu___117_1414.unfold_fully);
            unfold_attr = (uu___117_1414.unfold_attr);
            unfold_tac = (uu___117_1414.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1414.pure_subterms_within_computations);
            simplify = (uu___117_1414.simplify);
            erase_universes = (uu___117_1414.erase_universes);
            allow_unbound_universes = (uu___117_1414.allow_unbound_universes);
            reify_ = (uu___117_1414.reify_);
            compress_uvars = (uu___117_1414.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1414.check_no_uvars);
            unmeta = (uu___117_1414.unmeta);
            unascribe = (uu___117_1414.unascribe);
            in_full_norm_request = (uu___117_1414.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_1414.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___118_1415 = fs  in
          {
            beta = (uu___118_1415.beta);
            iota = (uu___118_1415.iota);
            zeta = (uu___118_1415.zeta);
            weak = (uu___118_1415.weak);
            hnf = (uu___118_1415.hnf);
            primops = (uu___118_1415.primops);
            do_not_unfold_pure_lets = (uu___118_1415.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1415.unfold_until);
            unfold_only = (uu___118_1415.unfold_only);
            unfold_fully = (uu___118_1415.unfold_fully);
            unfold_attr = (uu___118_1415.unfold_attr);
            unfold_tac = (uu___118_1415.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1415.pure_subterms_within_computations);
            simplify = (uu___118_1415.simplify);
            erase_universes = (uu___118_1415.erase_universes);
            allow_unbound_universes = (uu___118_1415.allow_unbound_universes);
            reify_ = (uu___118_1415.reify_);
            compress_uvars = (uu___118_1415.compress_uvars);
            no_full_norm = (uu___118_1415.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1415.unmeta);
            unascribe = (uu___118_1415.unascribe);
            in_full_norm_request = (uu___118_1415.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1415.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___119_1416 = fs  in
          {
            beta = (uu___119_1416.beta);
            iota = (uu___119_1416.iota);
            zeta = (uu___119_1416.zeta);
            weak = (uu___119_1416.weak);
            hnf = (uu___119_1416.hnf);
            primops = (uu___119_1416.primops);
            do_not_unfold_pure_lets = (uu___119_1416.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1416.unfold_until);
            unfold_only = (uu___119_1416.unfold_only);
            unfold_fully = (uu___119_1416.unfold_fully);
            unfold_attr = (uu___119_1416.unfold_attr);
            unfold_tac = (uu___119_1416.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1416.pure_subterms_within_computations);
            simplify = (uu___119_1416.simplify);
            erase_universes = (uu___119_1416.erase_universes);
            allow_unbound_universes = (uu___119_1416.allow_unbound_universes);
            reify_ = (uu___119_1416.reify_);
            compress_uvars = (uu___119_1416.compress_uvars);
            no_full_norm = (uu___119_1416.no_full_norm);
            check_no_uvars = (uu___119_1416.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1416.unascribe);
            in_full_norm_request = (uu___119_1416.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___119_1416.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___120_1417 = fs  in
          {
            beta = (uu___120_1417.beta);
            iota = (uu___120_1417.iota);
            zeta = (uu___120_1417.zeta);
            weak = (uu___120_1417.weak);
            hnf = (uu___120_1417.hnf);
            primops = (uu___120_1417.primops);
            do_not_unfold_pure_lets = (uu___120_1417.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1417.unfold_until);
            unfold_only = (uu___120_1417.unfold_only);
            unfold_fully = (uu___120_1417.unfold_fully);
            unfold_attr = (uu___120_1417.unfold_attr);
            unfold_tac = (uu___120_1417.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1417.pure_subterms_within_computations);
            simplify = (uu___120_1417.simplify);
            erase_universes = (uu___120_1417.erase_universes);
            allow_unbound_universes = (uu___120_1417.allow_unbound_universes);
            reify_ = (uu___120_1417.reify_);
            compress_uvars = (uu___120_1417.compress_uvars);
            no_full_norm = (uu___120_1417.no_full_norm);
            check_no_uvars = (uu___120_1417.check_no_uvars);
            unmeta = (uu___120_1417.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1417.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1417.weakly_reduce_scrutinee)
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1456  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1699 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1801 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1812 -> false
  
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
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
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
             let uu____2098 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2098 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2110 = FStar_Util.psmap_empty ()  in add_steps uu____2110 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2121 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2121
  
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
    match projectee with | Arg _0 -> true | uu____2267 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2303 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2339 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2410 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2458 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2514 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2556 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2594 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2630 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2646 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2671 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2671 with | (hd1,uu____2685) -> hd1
  
let mk :
  'Auu____2705 .
    'Auu____2705 ->
      FStar_Range.range -> 'Auu____2705 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2759 = FStar_ST.op_Bang r  in
          match uu____2759 with
          | FStar_Pervasives_Native.Some uu____2807 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____2875 =
      FStar_List.map
        (fun uu____2889  ->
           match uu____2889 with
           | (bopt,c) ->
               let uu____2902 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____2904 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____2902 uu____2904) env
       in
    FStar_All.pipe_right uu____2875 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_2907  ->
    match uu___79_2907 with
    | Clos (env,t,uu____2910,uu____2911) ->
        let uu____2956 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____2963 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____2956 uu____2963
    | Univ uu____2964 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2967  ->
    match uu___80_2967 with
    | Arg (c,uu____2969,uu____2970) ->
        let uu____2971 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2971
    | MemoLazy uu____2972 -> "MemoLazy"
    | Abs (uu____2979,bs,uu____2981,uu____2982,uu____2983) ->
        let uu____2988 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2988
    | UnivArgs uu____2993 -> "UnivArgs"
    | Match uu____3000 -> "Match"
    | App (uu____3009,t,uu____3011,uu____3012) ->
        let uu____3013 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3013
    | Meta (uu____3014,m,uu____3016) -> "Meta"
    | Let uu____3017 -> "Let"
    | Cfg uu____3026 -> "Cfg"
    | Debug (t,uu____3028) ->
        let uu____3029 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3029
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3037 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3037 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3068 . 'Auu____3068 Prims.list -> Prims.bool =
  fun uu___81_3074  ->
    match uu___81_3074 with | [] -> true | uu____3077 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3105 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3105
      with
      | uu____3124 ->
          let uu____3125 =
            let uu____3126 = FStar_Syntax_Print.db_to_string x  in
            let uu____3127 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3126
              uu____3127
             in
          failwith uu____3125
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3133 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3133
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3137 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3137
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3141 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3141
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
          let uu____3167 =
            FStar_List.fold_left
              (fun uu____3193  ->
                 fun u1  ->
                   match uu____3193 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3218 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3218 with
                        | (k_u,n1) ->
                            let uu____3233 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3233
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3167 with
          | (uu____3251,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3276 =
                   let uu____3277 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3277  in
                 match uu____3276 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3295 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3303 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3309 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3318 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3327 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3334 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3334 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3351 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3351 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3359 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3367 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3367 with
                                  | (uu____3372,m) -> n1 <= m))
                           in
                        if uu____3359 then rest1 else us1
                    | uu____3377 -> us1)
               | uu____3382 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3386 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3386
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3390 = aux u  in
           match uu____3390 with
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
            (fun uu____3494  ->
               let uu____3495 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3496 = env_to_string env  in
               let uu____3497 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3495 uu____3496 uu____3497);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3506 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3509 ->
                    let uu____3534 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3534
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3535 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3536 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3537 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3538 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3539 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3561 ->
                           let uu____3578 =
                             let uu____3579 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3580 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3579 uu____3580
                              in
                           failwith uu____3578
                       | uu____3583 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3589 =
                        let uu____3590 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3590  in
                      mk uu____3589 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3598 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3598  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3600 = lookup_bvar env x  in
                    (match uu____3600 with
                     | Univ uu____3603 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___125_3607 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___125_3607.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___125_3607.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3613,uu____3614) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3699  ->
                              fun stack1  ->
                                match uu____3699 with
                                | (a,aq) ->
                                    let uu____3711 =
                                      let uu____3712 =
                                        let uu____3719 =
                                          let uu____3720 =
                                            let uu____3751 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____3751, false)  in
                                          Clos uu____3720  in
                                        (uu____3719, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____3712  in
                                    uu____3711 :: stack1) args)
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
                    let uu____3945 = close_binders cfg env bs  in
                    (match uu____3945 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____3992 =
                      let uu____4003 =
                        let uu____4010 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4010]  in
                      close_binders cfg env uu____4003  in
                    (match uu____3992 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4033 =
                             let uu____4034 =
                               let uu____4041 =
                                 let uu____4042 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4042
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4041, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4034  in
                           mk uu____4033 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4133 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4133
                      | FStar_Util.Inr c ->
                          let uu____4147 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4147
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4166 =
                        let uu____4167 =
                          let uu____4194 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4194, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4167  in
                      mk uu____4166 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4240 =
                            let uu____4241 =
                              let uu____4248 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4248, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4241  in
                          mk uu____4240 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4300  -> dummy :: env1) env
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
                    let uu____4321 =
                      let uu____4332 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4332
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4351 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___126_4367 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_4367.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_4367.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4351))
                       in
                    (match uu____4321 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___127_4385 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_4385.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_4385.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_4385.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_4385.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4399,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4458  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4483 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4483
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4503  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4527 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4527
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___128_4535 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4535.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4535.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___129_4536 = lb  in
                      let uu____4537 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___129_4536.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___129_4536.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4537;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___129_4536.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___129_4536.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4569  -> fun env1  -> dummy :: env1)
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
            (fun uu____4672  ->
               let uu____4673 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4674 = env_to_string env  in
               let uu____4675 = stack_to_string stack  in
               let uu____4676 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4673 uu____4674 uu____4675 uu____4676);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4681,uu____4682),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____4757 = close_binders cfg env' bs  in
               (match uu____4757 with
                | (bs1,uu____4771) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____4787 =
                      let uu___130_4788 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___130_4788.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___130_4788.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____4787)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____4830 =
                 match uu____4830 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____4901 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____4922 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____4982  ->
                                     fun uu____4983  ->
                                       match (uu____4982, uu____4983) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5074 = norm_pat env4 p1
                                              in
                                           (match uu____5074 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____4922 with
                            | (pats1,env4) ->
                                ((let uu___131_5156 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___131_5156.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___132_5175 = x  in
                             let uu____5176 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___132_5175.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___132_5175.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5176
                             }  in
                           ((let uu___133_5190 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___133_5190.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___134_5201 = x  in
                             let uu____5202 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5201.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5201.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5202
                             }  in
                           ((let uu___135_5216 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5216.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___136_5232 = x  in
                             let uu____5233 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5232.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5232.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5233
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___137_5242 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5242.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5247 = norm_pat env2 pat  in
                     (match uu____5247 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5292 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5292
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5311 =
                   let uu____5312 =
                     let uu____5335 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5335)  in
                   FStar_Syntax_Syntax.Tm_match uu____5312  in
                 mk uu____5311 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5430 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5519  ->
                                       match uu____5519 with
                                       | (a,q) ->
                                           let uu____5538 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5538, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5430
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5549 =
                       let uu____5556 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5556)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5549
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5568 =
                       let uu____5577 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5577)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5568
                 | uu____5582 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5586 -> failwith "Impossible: unexpected stack element")

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
        let uu____5600 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5649  ->
                  fun uu____5650  ->
                    match (uu____5649, uu____5650) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_5720 = b  in
                          let uu____5721 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_5720.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_5720.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5721
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5600 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5814 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5827 = inline_closure_env cfg env [] t  in
                 let uu____5828 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5827 uu____5828
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5841 = inline_closure_env cfg env [] t  in
                 let uu____5842 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5841 uu____5842
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5888  ->
                           match uu____5888 with
                           | (a,q) ->
                               let uu____5901 =
                                 inline_closure_env cfg env [] a  in
                               (uu____5901, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5916  ->
                           match uu___82_5916 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5920 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5920
                           | f -> f))
                    in
                 let uu____5924 =
                   let uu___139_5925 = c1  in
                   let uu____5926 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5926;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_5925.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5924)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5936  ->
            match uu___83_5936 with
            | FStar_Syntax_Syntax.DECREASES uu____5937 -> false
            | uu____5940 -> true))

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
                   (fun uu___84_5958  ->
                      match uu___84_5958 with
                      | FStar_Syntax_Syntax.DECREASES uu____5959 -> false
                      | uu____5962 -> true))
               in
            let rc1 =
              let uu___140_5964 = rc  in
              let uu____5965 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_5964.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5965;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5974 -> lopt

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
    let uu____6065 =
      let uu____6072 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6072  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6065  in
  let arg_as_bounded_int uu____6096 =
    match uu____6096 with
    | (a,uu____6108) ->
        let uu____6115 =
          let uu____6116 = FStar_Syntax_Subst.compress a  in
          uu____6116.FStar_Syntax_Syntax.n  in
        (match uu____6115 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6126;
                FStar_Syntax_Syntax.vars = uu____6127;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6129;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6130;_},uu____6131)::[])
             when
             let uu____6170 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6170 "int_to_t" ->
             let uu____6171 =
               let uu____6176 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6176)  in
             FStar_Pervasives_Native.Some uu____6171
         | uu____6181 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6221 = f a  in FStar_Pervasives_Native.Some uu____6221
    | uu____6222 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6270 = f a0 a1  in FStar_Pervasives_Native.Some uu____6270
    | uu____6271 -> FStar_Pervasives_Native.None  in
  let unary_op a404 a405 a406 a407 a408 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6313 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a403  -> (Obj.magic (f res.psc_range)) a403)
                    uu____6313)) a404 a405 a406 a407 a408
     in
  let binary_op a411 a412 a413 a414 a415 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6362 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a409  ->
                       fun a410  -> (Obj.magic (f res.psc_range)) a409 a410)
                    uu____6362)) a411 a412 a413 a414 a415
     in
  let as_primitive_step is_strong uu____6389 =
    match uu____6389 with
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
    unary_op () (fun a416  -> (Obj.magic arg_as_int) a416)
      (fun a417  ->
         fun a418  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6437 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____6437)) a417 a418)
     in
  let binary_int_op f =
    binary_op () (fun a419  -> (Obj.magic arg_as_int) a419)
      (fun a420  ->
         fun a421  ->
           fun a422  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6465 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6465)) a420
               a421 a422)
     in
  let unary_bool_op f =
    unary_op () (fun a423  -> (Obj.magic arg_as_bool) a423)
      (fun a424  ->
         fun a425  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6486 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6486)) a424 a425)
     in
  let binary_bool_op f =
    binary_op () (fun a426  -> (Obj.magic arg_as_bool) a426)
      (fun a427  ->
         fun a428  ->
           fun a429  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6514 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6514)) a427
               a428 a429)
     in
  let binary_string_op f =
    binary_op () (fun a430  -> (Obj.magic arg_as_string) a430)
      (fun a431  ->
         fun a432  ->
           fun a433  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6542 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6542)) a431
               a432 a433)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6650 =
          let uu____6659 = as_a a  in
          let uu____6662 = as_b b  in (uu____6659, uu____6662)  in
        (match uu____6650 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6677 =
               let uu____6678 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6678  in
             FStar_Pervasives_Native.Some uu____6677
         | uu____6679 -> FStar_Pervasives_Native.None)
    | uu____6688 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6702 =
        let uu____6703 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6703  in
      mk uu____6702 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6713 =
      let uu____6716 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6716  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6713  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6748 =
      let uu____6749 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6749  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6748
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6767 = arg_as_string a1  in
        (match uu____6767 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6773 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6773 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6786 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6786
              | uu____6787 -> FStar_Pervasives_Native.None)
         | uu____6792 -> FStar_Pervasives_Native.None)
    | uu____6795 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6805 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6805
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6834 =
          let uu____6855 = arg_as_string fn  in
          let uu____6858 = arg_as_int from_line  in
          let uu____6861 = arg_as_int from_col  in
          let uu____6864 = arg_as_int to_line  in
          let uu____6867 = arg_as_int to_col  in
          (uu____6855, uu____6858, uu____6861, uu____6864, uu____6867)  in
        (match uu____6834 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6898 =
                 let uu____6899 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6900 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6899 uu____6900  in
               let uu____6901 =
                 let uu____6902 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6903 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6902 uu____6903  in
               FStar_Range.mk_range fn1 uu____6898 uu____6901  in
             let uu____6904 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6904
         | uu____6905 -> FStar_Pervasives_Native.None)
    | uu____6926 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6953)::(a1,uu____6955)::(a2,uu____6957)::[] ->
        let uu____6994 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6994 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7007 -> FStar_Pervasives_Native.None)
    | uu____7008 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7035)::[] ->
        let uu____7044 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7044 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7050 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7050
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7051 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7075 =
      let uu____7090 =
        let uu____7105 =
          let uu____7120 =
            let uu____7135 =
              let uu____7150 =
                let uu____7165 =
                  let uu____7180 =
                    let uu____7195 =
                      let uu____7210 =
                        let uu____7225 =
                          let uu____7240 =
                            let uu____7255 =
                              let uu____7270 =
                                let uu____7285 =
                                  let uu____7300 =
                                    let uu____7315 =
                                      let uu____7330 =
                                        let uu____7345 =
                                          let uu____7360 =
                                            let uu____7375 =
                                              let uu____7390 =
                                                let uu____7403 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7403,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a434  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a434)
                                                     (fun a435  ->
                                                        fun a436  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a435 a436)))
                                                 in
                                              let uu____7410 =
                                                let uu____7425 =
                                                  let uu____7438 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7438,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a437  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a437)
                                                       (fun a438  ->
                                                          fun a439  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a438 a439)))
                                                   in
                                                let uu____7445 =
                                                  let uu____7460 =
                                                    let uu____7475 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7475,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7484 =
                                                    let uu____7501 =
                                                      let uu____7516 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7516,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7501]  in
                                                  uu____7460 :: uu____7484
                                                   in
                                                uu____7425 :: uu____7445  in
                                              uu____7390 :: uu____7410  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7375
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7360
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a440  ->
                                                (Obj.magic arg_as_string)
                                                  a440)
                                             (fun a441  ->
                                                fun a442  ->
                                                  fun a443  ->
                                                    (Obj.magic
                                                       string_compare') a441
                                                      a442 a443)))
                                          :: uu____7345
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a444  ->
                                              (Obj.magic arg_as_bool) a444)
                                           (fun a445  ->
                                              fun a446  ->
                                                (Obj.magic string_of_bool1)
                                                  a445 a446)))
                                        :: uu____7330
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a447  ->
                                            (Obj.magic arg_as_int) a447)
                                         (fun a448  ->
                                            fun a449  ->
                                              (Obj.magic string_of_int1) a448
                                                a449)))
                                      :: uu____7315
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a450  ->
                                          (Obj.magic arg_as_int) a450)
                                       (fun a451  ->
                                          (Obj.magic arg_as_char) a451)
                                       (fun a452  ->
                                          fun a453  ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a452 a453)
                                       (fun a454  ->
                                          fun a455  ->
                                            fun a456  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____7707 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7707 y)) a454
                                                a455 a456)))
                                    :: uu____7300
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7285
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7270
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7255
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7240
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7225
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7210
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a457  -> (Obj.magic arg_as_int) a457)
                         (fun a458  ->
                            fun a459  ->
                              fun a460  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7874 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7874)) a458 a459 a460)))
                      :: uu____7195
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a461  -> (Obj.magic arg_as_int) a461)
                       (fun a462  ->
                          fun a463  ->
                            fun a464  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7900 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7900)) a462 a463 a464)))
                    :: uu____7180
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a465  -> (Obj.magic arg_as_int) a465)
                     (fun a466  ->
                        fun a467  ->
                          fun a468  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7926 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7926)) a466 a467 a468)))
                  :: uu____7165
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a469  -> (Obj.magic arg_as_int) a469)
                   (fun a470  ->
                      fun a471  ->
                        fun a472  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7952 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7952)) a470 a471 a472)))
                :: uu____7150
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7135
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7120
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7105
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7090
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7075
     in
  let weak_ops =
    let uu____8091 =
      let uu____8110 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8110, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8091]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8194 =
        let uu____8195 =
          let uu____8196 = FStar_Syntax_Syntax.as_arg c  in [uu____8196]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8195  in
      uu____8194 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8246 =
                let uu____8259 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____8259, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a473  -> (Obj.magic arg_as_bounded_int) a473)
                     (fun a474  ->
                        fun a475  ->
                          fun a476  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8275  ->
                                    fun uu____8276  ->
                                      match (uu____8275, uu____8276) with
                                      | ((int_to_t1,x),(uu____8295,y)) ->
                                          let uu____8305 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8305)) a474 a475 a476)))
                 in
              let uu____8306 =
                let uu____8321 =
                  let uu____8334 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____8334, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a477  -> (Obj.magic arg_as_bounded_int) a477)
                       (fun a478  ->
                          fun a479  ->
                            fun a480  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8350  ->
                                      fun uu____8351  ->
                                        match (uu____8350, uu____8351) with
                                        | ((int_to_t1,x),(uu____8370,y)) ->
                                            let uu____8380 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8380)) a478 a479 a480)))
                   in
                let uu____8381 =
                  let uu____8396 =
                    let uu____8409 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____8409, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a481  -> (Obj.magic arg_as_bounded_int) a481)
                         (fun a482  ->
                            fun a483  ->
                              fun a484  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8425  ->
                                        fun uu____8426  ->
                                          match (uu____8425, uu____8426) with
                                          | ((int_to_t1,x),(uu____8445,y)) ->
                                              let uu____8455 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8455)) a482 a483 a484)))
                     in
                  let uu____8456 =
                    let uu____8471 =
                      let uu____8484 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8484, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                           (fun a486  ->
                              fun a487  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8496  ->
                                        match uu____8496 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a486 a487)))
                       in
                    [uu____8471]  in
                  uu____8396 :: uu____8456  in
                uu____8321 :: uu____8381  in
              uu____8246 :: uu____8306))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8610 =
                let uu____8623 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8623, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a488  -> (Obj.magic arg_as_bounded_int) a488)
                     (fun a489  ->
                        fun a490  ->
                          fun a491  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8639  ->
                                    fun uu____8640  ->
                                      match (uu____8639, uu____8640) with
                                      | ((int_to_t1,x),(uu____8659,y)) ->
                                          let uu____8669 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8669)) a489 a490 a491)))
                 in
              let uu____8670 =
                let uu____8685 =
                  let uu____8698 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8698, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a492  -> (Obj.magic arg_as_bounded_int) a492)
                       (fun a493  ->
                          fun a494  ->
                            fun a495  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8714  ->
                                      fun uu____8715  ->
                                        match (uu____8714, uu____8715) with
                                        | ((int_to_t1,x),(uu____8734,y)) ->
                                            let uu____8744 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8744)) a493 a494 a495)))
                   in
                [uu____8685]  in
              uu____8610 :: uu____8670))
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
    | (_typ,uu____8856)::(a1,uu____8858)::(a2,uu____8860)::[] ->
        let uu____8897 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8897 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8903 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8903.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8903.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_8907 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_8907.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_8907.FStar_Syntax_Syntax.vars)
                })
         | uu____8908 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8910)::uu____8911::(a1,uu____8913)::(a2,uu____8915)::[] ->
        let uu____8964 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8964 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8970 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8970.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8970.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_8974 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_8974.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_8974.FStar_Syntax_Syntax.vars)
                })
         | uu____8975 -> FStar_Pervasives_Native.None)
    | uu____8976 -> failwith "Unexpected number of arguments"  in
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
    let uu____9028 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9028 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9073 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9073) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9133  ->
           fun subst1  ->
             match uu____9133 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9174,uu____9175)) ->
                      let uu____9234 = b  in
                      (match uu____9234 with
                       | (bv,uu____9242) ->
                           let uu____9243 =
                             let uu____9244 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____9244  in
                           if uu____9243
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____9249 = unembed_binder term1  in
                              match uu____9249 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____9256 =
                                      let uu___143_9257 = bv  in
                                      let uu____9258 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_9257.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_9257.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____9258
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____9256
                                     in
                                  let b_for_x =
                                    let uu____9262 =
                                      let uu____9269 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____9269)
                                       in
                                    FStar_Syntax_Syntax.NT uu____9262  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_9279  ->
                                         match uu___85_9279 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____9280,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9282;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9283;_})
                                             ->
                                             let uu____9288 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____9288
                                         | uu____9289 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____9290 -> subst1)) env []
  
let reduce_primops :
  'Auu____9307 'Auu____9308 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9307) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9308 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____9350 = FStar_Syntax_Util.head_and_args tm  in
             match uu____9350 with
             | (head1,args) ->
                 let uu____9387 =
                   let uu____9388 = FStar_Syntax_Util.un_uinst head1  in
                   uu____9388.FStar_Syntax_Syntax.n  in
                 (match uu____9387 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____9392 = find_prim_step cfg fv  in
                      (match uu____9392 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____9414  ->
                                   let uu____9415 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____9416 =
                                     FStar_Util.string_of_int l  in
                                   let uu____9423 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____9415 uu____9416 uu____9423);
                              tm)
                           else
                             (let uu____9425 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____9425 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9536  ->
                                        let uu____9537 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9537);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9540  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9542 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9542 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9548  ->
                                              let uu____9549 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9549);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9555  ->
                                              let uu____9556 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9557 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9556 uu____9557);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9558 ->
                           (log_primops cfg
                              (fun uu____9562  ->
                                 let uu____9563 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9563);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9567  ->
                            let uu____9568 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9568);
                       (match args with
                        | (a1,uu____9570)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9587 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9599  ->
                            let uu____9600 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9600);
                       (match args with
                        | (t,uu____9602)::(r,uu____9604)::[] ->
                            let uu____9631 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____9631 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___144_9635 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___144_9635.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___144_9635.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9638 -> tm))
                  | uu____9647 -> tm))
  
let reduce_equality :
  'Auu____9652 'Auu____9653 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9652) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9653 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_9691 = cfg  in
         {
           steps =
             (let uu___146_9694 = default_steps  in
              {
                beta = (uu___146_9694.beta);
                iota = (uu___146_9694.iota);
                zeta = (uu___146_9694.zeta);
                weak = (uu___146_9694.weak);
                hnf = (uu___146_9694.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_9694.do_not_unfold_pure_lets);
                unfold_until = (uu___146_9694.unfold_until);
                unfold_only = (uu___146_9694.unfold_only);
                unfold_fully = (uu___146_9694.unfold_fully);
                unfold_attr = (uu___146_9694.unfold_attr);
                unfold_tac = (uu___146_9694.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_9694.pure_subterms_within_computations);
                simplify = (uu___146_9694.simplify);
                erase_universes = (uu___146_9694.erase_universes);
                allow_unbound_universes =
                  (uu___146_9694.allow_unbound_universes);
                reify_ = (uu___146_9694.reify_);
                compress_uvars = (uu___146_9694.compress_uvars);
                no_full_norm = (uu___146_9694.no_full_norm);
                check_no_uvars = (uu___146_9694.check_no_uvars);
                unmeta = (uu___146_9694.unmeta);
                unascribe = (uu___146_9694.unascribe);
                in_full_norm_request = (uu___146_9694.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___146_9694.weakly_reduce_scrutinee)
              });
           tcenv = (uu___145_9691.tcenv);
           debug = (uu___145_9691.debug);
           delta_level = (uu___145_9691.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_9691.strong);
           memoize_lazy = (uu___145_9691.memoize_lazy);
           normalize_pure_lets = (uu___145_9691.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9698 .
    FStar_Syntax_Syntax.term -> 'Auu____9698 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9711 =
        let uu____9718 =
          let uu____9719 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9719.FStar_Syntax_Syntax.n  in
        (uu____9718, args)  in
      match uu____9711 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9725::uu____9726::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9730::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9735::uu____9736::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9739 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9750  ->
    match uu___86_9750 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9756 =
          let uu____9759 =
            let uu____9760 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9760  in
          [uu____9759]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____9756
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9766 =
          let uu____9769 =
            let uu____9770 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9770  in
          [uu____9769]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____9766
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9786 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9786) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9828 =
          let uu____9833 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9833 s  in
        match uu____9828 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9849 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9849
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9866::(tm,uu____9868)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9897)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9918)::uu____9919::(tm,uu____9921)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9958 =
            let uu____9963 = full_norm steps  in parse_steps uu____9963  in
          (match uu____9958 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10002 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_10019  ->
    match uu___87_10019 with
    | (App
        (uu____10022,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10023;
                       FStar_Syntax_Syntax.vars = uu____10024;_},uu____10025,uu____10026))::uu____10027
        -> true
    | uu____10034 -> false
  
let firstn :
  'Auu____10040 .
    Prims.int ->
      'Auu____10040 Prims.list ->
        ('Auu____10040 Prims.list,'Auu____10040 Prims.list)
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
          (uu____10076,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10077;
                         FStar_Syntax_Syntax.vars = uu____10078;_},uu____10079,uu____10080))::uu____10081
          -> (cfg.steps).reify_
      | uu____10088 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10107) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10117) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____10136  ->
                  match uu____10136 with
                  | (a,uu____10144) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10150 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____10175 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____10176 -> false
    | FStar_Syntax_Syntax.Tm_type uu____10193 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____10194 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____10195 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____10196 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____10197 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____10198 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____10205 -> false
    | FStar_Syntax_Syntax.Tm_let uu____10212 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____10225 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____10242 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____10255 -> true
    | FStar_Syntax_Syntax.Tm_match uu____10262 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____10324  ->
                   match uu____10324 with
                   | (a,uu____10332) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____10339) ->
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
                     (fun uu____10461  ->
                        match uu____10461 with
                        | (a,uu____10469) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____10474,uu____10475,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____10481,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____10487 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____10494 -> false
            | FStar_Syntax_Syntax.Meta_named uu____10495 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10677 ->
                   let uu____10702 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10702
               | uu____10703 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____10711  ->
               let uu____10712 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10713 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10714 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10721 =
                 let uu____10722 =
                   let uu____10725 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10725
                    in
                 stack_to_string uu____10722  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10712 uu____10713 uu____10714 uu____10721);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10748 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10749 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____10750 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10751;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_41;
                 FStar_Syntax_Syntax.fv_qual = uu____10752;_}
               when _0_41 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10755;
                 FStar_Syntax_Syntax.fv_delta = uu____10756;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10757;
                 FStar_Syntax_Syntax.fv_delta = uu____10758;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10759);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____10766 ->
               let uu____10773 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____10773
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10803 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10803)
               ->
               let cfg' =
                 let uu___147_10805 = cfg  in
                 {
                   steps =
                     (let uu___148_10808 = cfg.steps  in
                      {
                        beta = (uu___148_10808.beta);
                        iota = (uu___148_10808.iota);
                        zeta = (uu___148_10808.zeta);
                        weak = (uu___148_10808.weak);
                        hnf = (uu___148_10808.hnf);
                        primops = (uu___148_10808.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_10808.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_10808.unfold_attr);
                        unfold_tac = (uu___148_10808.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_10808.pure_subterms_within_computations);
                        simplify = (uu___148_10808.simplify);
                        erase_universes = (uu___148_10808.erase_universes);
                        allow_unbound_universes =
                          (uu___148_10808.allow_unbound_universes);
                        reify_ = (uu___148_10808.reify_);
                        compress_uvars = (uu___148_10808.compress_uvars);
                        no_full_norm = (uu___148_10808.no_full_norm);
                        check_no_uvars = (uu___148_10808.check_no_uvars);
                        unmeta = (uu___148_10808.unmeta);
                        unascribe = (uu___148_10808.unascribe);
                        in_full_norm_request =
                          (uu___148_10808.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___148_10808.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___147_10805.tcenv);
                   debug = (uu___147_10805.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___147_10805.primitive_steps);
                   strong = (uu___147_10805.strong);
                   memoize_lazy = (uu___147_10805.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10813 = get_norm_request (norm cfg' env []) args  in
               (match uu____10813 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10844  ->
                              fun stack1  ->
                                match uu____10844 with
                                | (a,aq) ->
                                    let uu____10856 =
                                      let uu____10857 =
                                        let uu____10864 =
                                          let uu____10865 =
                                            let uu____10896 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10896, false)  in
                                          Clos uu____10865  in
                                        (uu____10864, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10857  in
                                    uu____10856 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10980  ->
                          let uu____10981 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10981);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____11003 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_11008  ->
                                match uu___88_11008 with
                                | UnfoldUntil uu____11009 -> true
                                | UnfoldOnly uu____11010 -> true
                                | UnfoldFully uu____11013 -> true
                                | uu____11016 -> false))
                         in
                      if uu____11003
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_11021 = cfg  in
                      let uu____11022 =
                        let uu___150_11023 = to_fsteps s  in
                        {
                          beta = (uu___150_11023.beta);
                          iota = (uu___150_11023.iota);
                          zeta = (uu___150_11023.zeta);
                          weak = (uu___150_11023.weak);
                          hnf = (uu___150_11023.hnf);
                          primops = (uu___150_11023.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_11023.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_11023.unfold_until);
                          unfold_only = (uu___150_11023.unfold_only);
                          unfold_fully = (uu___150_11023.unfold_fully);
                          unfold_attr = (uu___150_11023.unfold_attr);
                          unfold_tac = (uu___150_11023.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_11023.pure_subterms_within_computations);
                          simplify = (uu___150_11023.simplify);
                          erase_universes = (uu___150_11023.erase_universes);
                          allow_unbound_universes =
                            (uu___150_11023.allow_unbound_universes);
                          reify_ = (uu___150_11023.reify_);
                          compress_uvars = (uu___150_11023.compress_uvars);
                          no_full_norm = (uu___150_11023.no_full_norm);
                          check_no_uvars = (uu___150_11023.check_no_uvars);
                          unmeta = (uu___150_11023.unmeta);
                          unascribe = (uu___150_11023.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___150_11023.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____11022;
                        tcenv = (uu___149_11021.tcenv);
                        debug = (uu___149_11021.debug);
                        delta_level;
                        primitive_steps = (uu___149_11021.primitive_steps);
                        strong = (uu___149_11021.strong);
                        memoize_lazy = (uu___149_11021.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____11032 =
                          let uu____11033 =
                            let uu____11038 = FStar_Util.now ()  in
                            (t1, uu____11038)  in
                          Debug uu____11033  in
                        uu____11032 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11042 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11042
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11051 =
                      let uu____11058 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11058, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11051  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____11068 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____11068  in
               let uu____11069 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____11069
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____11075  ->
                       let uu____11076 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11077 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____11076 uu____11077);
                  if b
                  then
                    (let uu____11078 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____11078 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____11086 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____11086) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____11099),uu____11100);
                                FStar_Syntax_Syntax.sigrng = uu____11101;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____11103;
                                FStar_Syntax_Syntax.sigattrs = uu____11104;_},uu____11105),uu____11106)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____11171 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_11175  ->
                               match uu___89_11175 with
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
                          (let uu____11185 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____11185))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____11204) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____11239,uu____11240) -> false)))
                     in
                  let uu____11257 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____11273 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____11273 then (true, true) else (false, false)
                     in
                  match uu____11257 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____11286  ->
                            let uu____11287 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____11288 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____11289 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____11287 uu____11288 uu____11289);
                       if should_delta2
                       then
                         (let uu____11290 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_11306 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_11309 = cfg.steps  in
                                      {
                                        beta = (uu___152_11309.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_11309.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_11309.unfold_attr);
                                        unfold_tac =
                                          (uu___152_11309.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_11309.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_11309.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_11309.allow_unbound_universes);
                                        reify_ = (uu___152_11309.reify_);
                                        compress_uvars =
                                          (uu___152_11309.compress_uvars);
                                        no_full_norm =
                                          (uu___152_11309.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_11309.check_no_uvars);
                                        unmeta = (uu___152_11309.unmeta);
                                        unascribe =
                                          (uu___152_11309.unascribe);
                                        in_full_norm_request =
                                          (uu___152_11309.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___152_11309.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___151_11306.tcenv);
                                   debug = (uu___151_11306.debug);
                                   delta_level = (uu___151_11306.delta_level);
                                   primitive_steps =
                                     (uu___151_11306.primitive_steps);
                                   strong = (uu___151_11306.strong);
                                   memoize_lazy =
                                     (uu___151_11306.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_11306.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____11290 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11323 = lookup_bvar env x  in
               (match uu____11323 with
                | Univ uu____11324 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____11373 = FStar_ST.op_Bang r  in
                      (match uu____11373 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11491  ->
                                 let uu____11492 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11493 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11492
                                   uu____11493);
                            (let uu____11494 = maybe_weakly_reduced t'  in
                             if uu____11494
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____11495 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11566)::uu____11567 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11576)::uu____11577 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11589,uu____11590))::stack_rest ->
                    (match c with
                     | Univ uu____11594 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11603 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11624  ->
                                    let uu____11625 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11625);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11665  ->
                                    let uu____11666 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11666);
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
                       (fun uu____11744  ->
                          let uu____11745 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11745);
                     norm cfg env stack1 t1)
                | (Debug uu____11746)::uu____11747 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11757 = cfg.steps  in
                             {
                               beta = (uu___153_11757.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11757.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11757.unfold_until);
                               unfold_only = (uu___153_11757.unfold_only);
                               unfold_fully = (uu___153_11757.unfold_fully);
                               unfold_attr = (uu___153_11757.unfold_attr);
                               unfold_tac = (uu___153_11757.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11757.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11757.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11757.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11757.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11757.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_11757.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_11759 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11759.tcenv);
                               debug = (uu___154_11759.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11759.primitive_steps);
                               strong = (uu___154_11759.strong);
                               memoize_lazy = (uu___154_11759.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11759.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11761 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11761 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11803  -> dummy :: env1) env)
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
                                          let uu____11840 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11840)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11845 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11845.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11845.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11846 -> lopt  in
                           (log cfg
                              (fun uu____11852  ->
                                 let uu____11853 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11853);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11862 = cfg  in
                               {
                                 steps = (uu___156_11862.steps);
                                 tcenv = (uu___156_11862.tcenv);
                                 debug = (uu___156_11862.debug);
                                 delta_level = (uu___156_11862.delta_level);
                                 primitive_steps =
                                   (uu___156_11862.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11862.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11862.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11873)::uu____11874 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11886 = cfg.steps  in
                             {
                               beta = (uu___153_11886.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11886.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11886.unfold_until);
                               unfold_only = (uu___153_11886.unfold_only);
                               unfold_fully = (uu___153_11886.unfold_fully);
                               unfold_attr = (uu___153_11886.unfold_attr);
                               unfold_tac = (uu___153_11886.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11886.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11886.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11886.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11886.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11886.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_11886.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_11888 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11888.tcenv);
                               debug = (uu___154_11888.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11888.primitive_steps);
                               strong = (uu___154_11888.strong);
                               memoize_lazy = (uu___154_11888.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11888.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11890 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11890 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11932  -> dummy :: env1) env)
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
                                          let uu____11969 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11969)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11974 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11974.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11974.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11975 -> lopt  in
                           (log cfg
                              (fun uu____11981  ->
                                 let uu____11982 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11982);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11991 = cfg  in
                               {
                                 steps = (uu___156_11991.steps);
                                 tcenv = (uu___156_11991.tcenv);
                                 debug = (uu___156_11991.debug);
                                 delta_level = (uu___156_11991.delta_level);
                                 primitive_steps =
                                   (uu___156_11991.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11991.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11991.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12002)::uu____12003 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12017 = cfg.steps  in
                             {
                               beta = (uu___153_12017.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12017.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12017.unfold_until);
                               unfold_only = (uu___153_12017.unfold_only);
                               unfold_fully = (uu___153_12017.unfold_fully);
                               unfold_attr = (uu___153_12017.unfold_attr);
                               unfold_tac = (uu___153_12017.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12017.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12017.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12017.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12017.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12017.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12017.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12019 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12019.tcenv);
                               debug = (uu___154_12019.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12019.primitive_steps);
                               strong = (uu___154_12019.strong);
                               memoize_lazy = (uu___154_12019.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12019.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12021 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12021 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12063  -> dummy :: env1) env)
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
                                          let uu____12100 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12100)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12105 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12105.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12105.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12106 -> lopt  in
                           (log cfg
                              (fun uu____12112  ->
                                 let uu____12113 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12113);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12122 = cfg  in
                               {
                                 steps = (uu___156_12122.steps);
                                 tcenv = (uu___156_12122.tcenv);
                                 debug = (uu___156_12122.debug);
                                 delta_level = (uu___156_12122.delta_level);
                                 primitive_steps =
                                   (uu___156_12122.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12122.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12122.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12133)::uu____12134 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12148 = cfg.steps  in
                             {
                               beta = (uu___153_12148.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12148.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12148.unfold_until);
                               unfold_only = (uu___153_12148.unfold_only);
                               unfold_fully = (uu___153_12148.unfold_fully);
                               unfold_attr = (uu___153_12148.unfold_attr);
                               unfold_tac = (uu___153_12148.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12148.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12148.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12148.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12148.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12148.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12148.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12150 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12150.tcenv);
                               debug = (uu___154_12150.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12150.primitive_steps);
                               strong = (uu___154_12150.strong);
                               memoize_lazy = (uu___154_12150.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12150.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12152 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12152 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12194  -> dummy :: env1) env)
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
                                          let uu____12231 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12231)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12236 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12236.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12236.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12237 -> lopt  in
                           (log cfg
                              (fun uu____12243  ->
                                 let uu____12244 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12244);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12253 = cfg  in
                               {
                                 steps = (uu___156_12253.steps);
                                 tcenv = (uu___156_12253.tcenv);
                                 debug = (uu___156_12253.debug);
                                 delta_level = (uu___156_12253.delta_level);
                                 primitive_steps =
                                   (uu___156_12253.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12253.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12253.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12264)::uu____12265 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12283 = cfg.steps  in
                             {
                               beta = (uu___153_12283.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12283.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12283.unfold_until);
                               unfold_only = (uu___153_12283.unfold_only);
                               unfold_fully = (uu___153_12283.unfold_fully);
                               unfold_attr = (uu___153_12283.unfold_attr);
                               unfold_tac = (uu___153_12283.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12283.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12283.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12283.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12283.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12283.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12283.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12285 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12285.tcenv);
                               debug = (uu___154_12285.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12285.primitive_steps);
                               strong = (uu___154_12285.strong);
                               memoize_lazy = (uu___154_12285.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12285.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12287 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12287 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12329  -> dummy :: env1) env)
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
                                          let uu____12366 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12366)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12371 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12371.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12371.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12372 -> lopt  in
                           (log cfg
                              (fun uu____12378  ->
                                 let uu____12379 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12379);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12388 = cfg  in
                               {
                                 steps = (uu___156_12388.steps);
                                 tcenv = (uu___156_12388.tcenv);
                                 debug = (uu___156_12388.debug);
                                 delta_level = (uu___156_12388.delta_level);
                                 primitive_steps =
                                   (uu___156_12388.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12388.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12388.normalize_pure_lets)
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
                             let uu___153_12402 = cfg.steps  in
                             {
                               beta = (uu___153_12402.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12402.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12402.unfold_until);
                               unfold_only = (uu___153_12402.unfold_only);
                               unfold_fully = (uu___153_12402.unfold_fully);
                               unfold_attr = (uu___153_12402.unfold_attr);
                               unfold_tac = (uu___153_12402.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12402.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12402.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12402.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12402.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12402.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12402.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12404 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12404.tcenv);
                               debug = (uu___154_12404.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12404.primitive_steps);
                               strong = (uu___154_12404.strong);
                               memoize_lazy = (uu___154_12404.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12404.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12406 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12406 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12448  -> dummy :: env1) env)
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
                                          let uu____12485 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12485)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12490 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12490.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12490.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12491 -> lopt  in
                           (log cfg
                              (fun uu____12497  ->
                                 let uu____12498 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12498);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12507 = cfg  in
                               {
                                 steps = (uu___156_12507.steps);
                                 tcenv = (uu___156_12507.tcenv);
                                 debug = (uu___156_12507.debug);
                                 delta_level = (uu___156_12507.delta_level);
                                 primitive_steps =
                                   (uu___156_12507.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12507.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12507.normalize_pure_lets)
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
                      (fun uu____12556  ->
                         fun stack1  ->
                           match uu____12556 with
                           | (a,aq) ->
                               let uu____12568 =
                                 let uu____12569 =
                                   let uu____12576 =
                                     let uu____12577 =
                                       let uu____12608 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12608, false)  in
                                     Clos uu____12577  in
                                   (uu____12576, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12569  in
                               uu____12568 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12692  ->
                     let uu____12693 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12693);
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
                             ((let uu___157_12729 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12729.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12729.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12730 ->
                      let uu____12735 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12735)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12738 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12738 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12769 =
                          let uu____12770 =
                            let uu____12777 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_12779 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_12779.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_12779.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12777)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12770  in
                        mk uu____12769 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12798 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12798
               else
                 (let uu____12800 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12800 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12808 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12832  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12808 c1  in
                      let t2 =
                        let uu____12854 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12854 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12965)::uu____12966 ->
                    (log cfg
                       (fun uu____12979  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12980)::uu____12981 ->
                    (log cfg
                       (fun uu____12992  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12993,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12994;
                                   FStar_Syntax_Syntax.vars = uu____12995;_},uu____12996,uu____12997))::uu____12998
                    ->
                    (log cfg
                       (fun uu____13007  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13008)::uu____13009 ->
                    (log cfg
                       (fun uu____13020  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13021 ->
                    (log cfg
                       (fun uu____13024  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13028  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13045 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13045
                         | FStar_Util.Inr c ->
                             let uu____13053 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13053
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13066 =
                               let uu____13067 =
                                 let uu____13094 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13094, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13067
                                in
                             mk uu____13066 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____13113 ->
                           let uu____13114 =
                             let uu____13115 =
                               let uu____13116 =
                                 let uu____13143 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13143, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13116
                                in
                             mk uu____13115 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____13114))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___159_13220 = cfg  in
                   {
                     steps =
                       (let uu___160_13223 = cfg.steps  in
                        {
                          beta = (uu___160_13223.beta);
                          iota = (uu___160_13223.iota);
                          zeta = (uu___160_13223.zeta);
                          weak = true;
                          hnf = (uu___160_13223.hnf);
                          primops = (uu___160_13223.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_13223.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_13223.unfold_until);
                          unfold_only = (uu___160_13223.unfold_only);
                          unfold_fully = (uu___160_13223.unfold_fully);
                          unfold_attr = (uu___160_13223.unfold_attr);
                          unfold_tac = (uu___160_13223.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_13223.pure_subterms_within_computations);
                          simplify = (uu___160_13223.simplify);
                          erase_universes = (uu___160_13223.erase_universes);
                          allow_unbound_universes =
                            (uu___160_13223.allow_unbound_universes);
                          reify_ = (uu___160_13223.reify_);
                          compress_uvars = (uu___160_13223.compress_uvars);
                          no_full_norm = (uu___160_13223.no_full_norm);
                          check_no_uvars = (uu___160_13223.check_no_uvars);
                          unmeta = (uu___160_13223.unmeta);
                          unascribe = (uu___160_13223.unascribe);
                          in_full_norm_request =
                            (uu___160_13223.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___160_13223.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___159_13220.tcenv);
                     debug = (uu___159_13220.debug);
                     delta_level = (uu___159_13220.delta_level);
                     primitive_steps = (uu___159_13220.primitive_steps);
                     strong = (uu___159_13220.strong);
                     memoize_lazy = (uu___159_13220.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_13220.normalize_pure_lets)
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
                         let uu____13259 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13259 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_13279 = cfg  in
                               let uu____13280 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_13279.steps);
                                 tcenv = uu____13280;
                                 debug = (uu___161_13279.debug);
                                 delta_level = (uu___161_13279.delta_level);
                                 primitive_steps =
                                   (uu___161_13279.primitive_steps);
                                 strong = (uu___161_13279.strong);
                                 memoize_lazy = (uu___161_13279.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_13279.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____13285 =
                                 let uu____13286 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13286  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13285
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_13289 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_13289.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_13289.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_13289.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_13289.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____13290 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13290
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13301,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13302;
                               FStar_Syntax_Syntax.lbunivs = uu____13303;
                               FStar_Syntax_Syntax.lbtyp = uu____13304;
                               FStar_Syntax_Syntax.lbeff = uu____13305;
                               FStar_Syntax_Syntax.lbdef = uu____13306;
                               FStar_Syntax_Syntax.lbattrs = uu____13307;
                               FStar_Syntax_Syntax.lbpos = uu____13308;_}::uu____13309),uu____13310)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13350 =
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
               if uu____13350
               then
                 let binder =
                   let uu____13352 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13352  in
                 let env1 =
                   let uu____13362 =
                     let uu____13369 =
                       let uu____13370 =
                         let uu____13401 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13401,
                           false)
                          in
                       Clos uu____13370  in
                     ((FStar_Pervasives_Native.Some binder), uu____13369)  in
                   uu____13362 :: env  in
                 (log cfg
                    (fun uu____13494  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____13498  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13499 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13499))
                 else
                   (let uu____13501 =
                      let uu____13506 =
                        let uu____13507 =
                          let uu____13508 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____13508
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____13507]  in
                      FStar_Syntax_Subst.open_term uu____13506 body  in
                    match uu____13501 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13517  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____13525 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____13525  in
                            FStar_Util.Inl
                              (let uu___163_13535 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_13535.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_13535.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____13538  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_13540 = lb  in
                             let uu____13541 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_13540.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_13540.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13541;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_13540.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_13540.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13576  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_13599 = cfg  in
                             {
                               steps = (uu___165_13599.steps);
                               tcenv = (uu___165_13599.tcenv);
                               debug = (uu___165_13599.debug);
                               delta_level = (uu___165_13599.delta_level);
                               primitive_steps =
                                 (uu___165_13599.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_13599.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_13599.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13602  ->
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
               let uu____13619 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13619 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13655 =
                               let uu___166_13656 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_13656.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_13656.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13655  in
                           let uu____13657 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13657 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13683 =
                                   FStar_List.map (fun uu____13699  -> dummy)
                                     lbs1
                                    in
                                 let uu____13700 =
                                   let uu____13709 =
                                     FStar_List.map
                                       (fun uu____13729  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13709 env  in
                                 FStar_List.append uu____13683 uu____13700
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13753 =
                                       let uu___167_13754 = rc  in
                                       let uu____13755 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_13754.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13755;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_13754.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13753
                                 | uu____13762 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_13766 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_13766.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_13766.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_13766.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_13766.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13776 =
                        FStar_List.map (fun uu____13792  -> dummy) lbs2  in
                      FStar_List.append uu____13776 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13800 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13800 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_13816 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_13816.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_13816.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13843 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13843
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13862 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13938  ->
                        match uu____13938 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_14059 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_14059.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_14059.FStar_Syntax_Syntax.sort)
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
               (match uu____13862 with
                | (rec_env,memos,uu____14272) ->
                    let uu____14325 =
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
                             let uu____14636 =
                               let uu____14643 =
                                 let uu____14644 =
                                   let uu____14675 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14675, false)
                                    in
                                 Clos uu____14644  in
                               (FStar_Pervasives_Native.None, uu____14643)
                                in
                             uu____14636 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14785  ->
                     let uu____14786 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14786);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14808 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14810::uu____14811 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14816) ->
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
                             | uu____14839 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14853 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14853
                              | uu____14864 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14868 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14894 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14912 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14929 =
                        let uu____14930 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14931 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14930 uu____14931
                         in
                      failwith uu____14929
                    else rebuild cfg env stack t2
                | uu____14933 -> norm cfg env stack t2))

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
                let uu____14943 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14943  in
              let uu____14944 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14944 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14957  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____14968  ->
                        let uu____14969 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14970 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14969 uu____14970);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____14975 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____14975 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14984))::stack1 ->
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
                      | uu____15039 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15042 ->
                          let uu____15045 =
                            let uu____15046 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15046
                             in
                          failwith uu____15045
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
                  let uu___171_15070 = cfg  in
                  let uu____15071 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____15071;
                    tcenv = (uu___171_15070.tcenv);
                    debug = (uu___171_15070.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_15070.primitive_steps);
                    strong = (uu___171_15070.strong);
                    memoize_lazy = (uu___171_15070.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_15070.normalize_pure_lets)
                  }
                else
                  (let uu___172_15073 = cfg  in
                   {
                     steps =
                       (let uu___173_15076 = cfg.steps  in
                        {
                          beta = (uu___173_15076.beta);
                          iota = (uu___173_15076.iota);
                          zeta = false;
                          weak = (uu___173_15076.weak);
                          hnf = (uu___173_15076.hnf);
                          primops = (uu___173_15076.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_15076.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_15076.unfold_until);
                          unfold_only = (uu___173_15076.unfold_only);
                          unfold_fully = (uu___173_15076.unfold_fully);
                          unfold_attr = (uu___173_15076.unfold_attr);
                          unfold_tac = (uu___173_15076.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_15076.pure_subterms_within_computations);
                          simplify = (uu___173_15076.simplify);
                          erase_universes = (uu___173_15076.erase_universes);
                          allow_unbound_universes =
                            (uu___173_15076.allow_unbound_universes);
                          reify_ = (uu___173_15076.reify_);
                          compress_uvars = (uu___173_15076.compress_uvars);
                          no_full_norm = (uu___173_15076.no_full_norm);
                          check_no_uvars = (uu___173_15076.check_no_uvars);
                          unmeta = (uu___173_15076.unmeta);
                          unascribe = (uu___173_15076.unascribe);
                          in_full_norm_request =
                            (uu___173_15076.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___173_15076.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___172_15073.tcenv);
                     debug = (uu___172_15073.debug);
                     delta_level = (uu___172_15073.delta_level);
                     primitive_steps = (uu___172_15073.primitive_steps);
                     strong = (uu___172_15073.strong);
                     memoize_lazy = (uu___172_15073.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_15073.normalize_pure_lets)
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
                  (fun uu____15106  ->
                     let uu____15107 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____15108 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15107
                       uu____15108);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____15110 =
                   let uu____15111 = FStar_Syntax_Subst.compress head3  in
                   uu____15111.FStar_Syntax_Syntax.n  in
                 match uu____15110 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____15129 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15129
                        in
                     let uu____15130 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15130 with
                      | (uu____15131,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15137 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15145 =
                                   let uu____15146 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____15146.FStar_Syntax_Syntax.n  in
                                 match uu____15145 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15152,uu____15153))
                                     ->
                                     let uu____15162 =
                                       let uu____15163 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____15163.FStar_Syntax_Syntax.n  in
                                     (match uu____15162 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15169,msrc,uu____15171))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15180 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15180
                                      | uu____15181 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15182 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____15183 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____15183 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_15188 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_15188.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_15188.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_15188.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_15188.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_15188.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____15189 = FStar_List.tl stack  in
                                    let uu____15190 =
                                      let uu____15191 =
                                        let uu____15194 =
                                          let uu____15195 =
                                            let uu____15208 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____15208)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15195
                                           in
                                        FStar_Syntax_Syntax.mk uu____15194
                                         in
                                      uu____15191
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____15189 uu____15190
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15224 =
                                      let uu____15225 = is_return body  in
                                      match uu____15225 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15229;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15230;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15235 -> false  in
                                    if uu____15224
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
                                         let uu____15258 =
                                           let uu____15261 =
                                             let uu____15262 =
                                               let uu____15279 =
                                                 let uu____15282 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____15282]  in
                                               (uu____15279, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15262
                                              in
                                           FStar_Syntax_Syntax.mk uu____15261
                                            in
                                         uu____15258
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____15298 =
                                           let uu____15299 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____15299.FStar_Syntax_Syntax.n
                                            in
                                         match uu____15298 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15305::uu____15306::[])
                                             ->
                                             let uu____15313 =
                                               let uu____15316 =
                                                 let uu____15317 =
                                                   let uu____15324 =
                                                     let uu____15327 =
                                                       let uu____15328 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15328
                                                        in
                                                     let uu____15329 =
                                                       let uu____15332 =
                                                         let uu____15333 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15333
                                                          in
                                                       [uu____15332]  in
                                                     uu____15327 ::
                                                       uu____15329
                                                      in
                                                   (bind1, uu____15324)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15317
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15316
                                                in
                                             uu____15313
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15341 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____15347 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____15347
                                         then
                                           let uu____15350 =
                                             let uu____15351 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____15351
                                              in
                                           let uu____15352 =
                                             let uu____15355 =
                                               let uu____15356 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____15356
                                                in
                                             [uu____15355]  in
                                           uu____15350 :: uu____15352
                                         else []  in
                                       let reified =
                                         let uu____15361 =
                                           let uu____15364 =
                                             let uu____15365 =
                                               let uu____15380 =
                                                 let uu____15383 =
                                                   let uu____15386 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____15387 =
                                                     let uu____15390 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____15390]  in
                                                   uu____15386 :: uu____15387
                                                    in
                                                 let uu____15391 =
                                                   let uu____15394 =
                                                     let uu____15397 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____15398 =
                                                       let uu____15401 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____15402 =
                                                         let uu____15405 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____15406 =
                                                           let uu____15409 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____15409]  in
                                                         uu____15405 ::
                                                           uu____15406
                                                          in
                                                       uu____15401 ::
                                                         uu____15402
                                                        in
                                                     uu____15397 ::
                                                       uu____15398
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____15394
                                                    in
                                                 FStar_List.append
                                                   uu____15383 uu____15391
                                                  in
                                               (bind_inst, uu____15380)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15365
                                              in
                                           FStar_Syntax_Syntax.mk uu____15364
                                            in
                                         uu____15361
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____15421  ->
                                            let uu____15422 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____15423 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15422 uu____15423);
                                       (let uu____15424 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____15424 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____15448 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15448
                        in
                     let uu____15449 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15449 with
                      | (uu____15450,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15485 =
                                  let uu____15486 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15486.FStar_Syntax_Syntax.n  in
                                match uu____15485 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15492) -> t2
                                | uu____15497 -> head4  in
                              let uu____15498 =
                                let uu____15499 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15499.FStar_Syntax_Syntax.n  in
                              match uu____15498 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15505 -> FStar_Pervasives_Native.None
                               in
                            let uu____15506 = maybe_extract_fv head4  in
                            match uu____15506 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15516 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15516
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____15521 = maybe_extract_fv head5
                                     in
                                  match uu____15521 with
                                  | FStar_Pervasives_Native.Some uu____15526
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15527 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____15532 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15547 =
                              match uu____15547 with
                              | (e,q) ->
                                  let uu____15554 =
                                    let uu____15555 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15555.FStar_Syntax_Syntax.n  in
                                  (match uu____15554 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____15570 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____15570
                                   | uu____15571 -> false)
                               in
                            let uu____15572 =
                              let uu____15573 =
                                let uu____15580 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15580 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15573
                               in
                            if uu____15572
                            then
                              let uu____15585 =
                                let uu____15586 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15586
                                 in
                              failwith uu____15585
                            else ());
                           (let uu____15588 = maybe_unfold_action head_app
                               in
                            match uu____15588 with
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
                                   (fun uu____15629  ->
                                      let uu____15630 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15631 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15630 uu____15631);
                                 (let uu____15632 = FStar_List.tl stack  in
                                  norm cfg env uu____15632 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15634) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15658 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15658  in
                     (log cfg
                        (fun uu____15662  ->
                           let uu____15663 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15663);
                      (let uu____15664 = FStar_List.tl stack  in
                       norm cfg env uu____15664 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15785  ->
                               match uu____15785 with
                               | (pat,wopt,tm) ->
                                   let uu____15833 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15833)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15865 = FStar_List.tl stack  in
                     norm cfg env uu____15865 tm
                 | uu____15866 -> fallback ())

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
              (fun uu____15880  ->
                 let uu____15881 = FStar_Ident.string_of_lid msrc  in
                 let uu____15882 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15883 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15881
                   uu____15882 uu____15883);
            (let uu____15884 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15884
             then
               let ed =
                 let uu____15886 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15886  in
               let uu____15887 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15887 with
               | (uu____15888,return_repr) ->
                   let return_inst =
                     let uu____15897 =
                       let uu____15898 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15898.FStar_Syntax_Syntax.n  in
                     match uu____15897 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15904::[]) ->
                         let uu____15911 =
                           let uu____15914 =
                             let uu____15915 =
                               let uu____15922 =
                                 let uu____15925 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15925]  in
                               (return_tm, uu____15922)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15915  in
                           FStar_Syntax_Syntax.mk uu____15914  in
                         uu____15911 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15933 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15936 =
                     let uu____15939 =
                       let uu____15940 =
                         let uu____15955 =
                           let uu____15958 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15959 =
                             let uu____15962 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15962]  in
                           uu____15958 :: uu____15959  in
                         (return_inst, uu____15955)  in
                       FStar_Syntax_Syntax.Tm_app uu____15940  in
                     FStar_Syntax_Syntax.mk uu____15939  in
                   uu____15936 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15971 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15971 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15974 =
                      let uu____15975 = FStar_Ident.text_of_lid msrc  in
                      let uu____15976 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15975 uu____15976
                       in
                    failwith uu____15974
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15977;
                      FStar_TypeChecker_Env.mtarget = uu____15978;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15979;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15994 =
                      let uu____15995 = FStar_Ident.text_of_lid msrc  in
                      let uu____15996 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15995 uu____15996
                       in
                    failwith uu____15994
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15997;
                      FStar_TypeChecker_Env.mtarget = uu____15998;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15999;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16023 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16024 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16023 t FStar_Syntax_Syntax.tun uu____16024))

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
                (fun uu____16080  ->
                   match uu____16080 with
                   | (a,imp) ->
                       let uu____16091 = norm cfg env [] a  in
                       (uu____16091, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____16099  ->
             let uu____16100 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16101 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____16100 uu____16101);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16125 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____16125
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_16128 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_16128.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_16128.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16148 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____16148
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_16151 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_16151.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_16151.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16184  ->
                      match uu____16184 with
                      | (a,i) ->
                          let uu____16195 = norm cfg env [] a  in
                          (uu____16195, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_16213  ->
                       match uu___90_16213 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16217 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16217
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_16225 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_16228 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_16228.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_16225.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_16225.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16231  ->
        match uu____16231 with
        | (x,imp) ->
            let uu____16234 =
              let uu___179_16235 = x  in
              let uu____16236 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_16235.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_16235.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16236
              }  in
            (uu____16234, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16242 =
          FStar_List.fold_left
            (fun uu____16260  ->
               fun b  ->
                 match uu____16260 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16242 with | (nbs,uu____16300) -> FStar_List.rev nbs

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
            let uu____16316 =
              let uu___180_16317 = rc  in
              let uu____16318 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_16317.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16318;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_16317.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16316
        | uu____16325 -> lopt

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
            (let uu____16346 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16347 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____16346
               uu____16347)
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
          let uu____16367 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____16367
          then tm1
          else
            (let w t =
               let uu___181_16379 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_16379.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_16379.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16388 =
                 let uu____16389 = FStar_Syntax_Util.unmeta t  in
                 uu____16389.FStar_Syntax_Syntax.n  in
               match uu____16388 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16396 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16441)::args1,(bv,uu____16444)::bs1) ->
                   let uu____16478 =
                     let uu____16479 = FStar_Syntax_Subst.compress t  in
                     uu____16479.FStar_Syntax_Syntax.n  in
                   (match uu____16478 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16483 -> false)
               | ([],[]) -> true
               | (uu____16504,uu____16505) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____16542 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16543 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16542
                    uu____16543)
               else ();
               (let uu____16545 = FStar_Syntax_Util.head_and_args' t  in
                match uu____16545 with
                | (hd1,args) ->
                    let uu____16578 =
                      let uu____16579 = FStar_Syntax_Subst.compress hd1  in
                      uu____16579.FStar_Syntax_Syntax.n  in
                    (match uu____16578 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____16586 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____16587 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____16588 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16586 uu____16587 uu____16588)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16590 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____16603 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16604 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16603
                    uu____16604)
               else ();
               (let uu____16606 = FStar_Syntax_Util.is_squash t  in
                match uu____16606 with
                | FStar_Pervasives_Native.Some (uu____16617,t') ->
                    is_applied bs t'
                | uu____16629 ->
                    let uu____16638 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____16638 with
                     | FStar_Pervasives_Native.Some (uu____16649,t') ->
                         is_applied bs t'
                     | uu____16661 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____16681 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16681 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16688)::(q,uu____16690)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____16726 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____16727 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____16726 uu____16727)
                    else ();
                    (let uu____16729 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____16729 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16734 =
                           let uu____16735 = FStar_Syntax_Subst.compress p
                              in
                           uu____16735.FStar_Syntax_Syntax.n  in
                         (match uu____16734 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____16743 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____16743))
                          | uu____16744 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____16747)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____16772 =
                           let uu____16773 = FStar_Syntax_Subst.compress p1
                              in
                           uu____16773.FStar_Syntax_Syntax.n  in
                         (match uu____16772 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____16781 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____16781))
                          | uu____16782 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____16786 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____16786 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____16791 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____16791 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if (cfg.debug).wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 3\n"
                                    else ();
                                    (let ftrue =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_true
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____16800 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____16800))
                               | uu____16801 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____16806)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____16831 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____16831 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if (cfg.debug).wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 4\n"
                                    else ();
                                    (let ffalse =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_false
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____16840 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____16840))
                               | uu____16841 -> FStar_Pervasives_Native.None)
                          | uu____16844 -> FStar_Pervasives_Native.None)
                     | uu____16847 -> FStar_Pervasives_Native.None))
               | uu____16850 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____16861 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16861 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____16867)::[],uu____16868,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____16885 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____16886 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____16885
                         uu____16886)
                    else ();
                    is_quantified_const bv phi')
               | uu____16888 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16899 =
                 let uu____16900 = FStar_Syntax_Subst.compress phi  in
                 uu____16900.FStar_Syntax_Syntax.n  in
               match uu____16899 with
               | FStar_Syntax_Syntax.Tm_match (uu____16905,br::brs) ->
                   let uu____16972 = br  in
                   (match uu____16972 with
                    | (uu____16989,uu____16990,e) ->
                        let r =
                          let uu____17011 = simp_t e  in
                          match uu____17011 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17017 =
                                FStar_List.for_all
                                  (fun uu____17035  ->
                                     match uu____17035 with
                                     | (uu____17048,uu____17049,e') ->
                                         let uu____17063 = simp_t e'  in
                                         uu____17063 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17017
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17071 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17076 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17076
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17097 =
                 match uu____17097 with
                 | (t1,q) ->
                     let uu____17110 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17110 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17138 -> (t1, q))
                  in
               let uu____17147 = FStar_Syntax_Util.head_and_args t  in
               match uu____17147 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____17209 =
                 let uu____17210 = FStar_Syntax_Util.unmeta ty  in
                 uu____17210.FStar_Syntax_Syntax.n  in
               match uu____17209 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17214) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17219,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17239 -> false  in
             let simplify1 arg =
               let uu____17262 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17262, arg)  in
             let uu____17271 = is_forall_const tm1  in
             match uu____17271 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____17276 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____17277 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17276
                       uu____17277)
                  else ();
                  (let uu____17279 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____17279))
             | FStar_Pervasives_Native.None  ->
                 let uu____17280 =
                   let uu____17281 = FStar_Syntax_Subst.compress tm1  in
                   uu____17281.FStar_Syntax_Syntax.n  in
                 (match uu____17280 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17285;
                              FStar_Syntax_Syntax.vars = uu____17286;_},uu____17287);
                         FStar_Syntax_Syntax.pos = uu____17288;
                         FStar_Syntax_Syntax.vars = uu____17289;_},args)
                      ->
                      let uu____17315 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17315
                      then
                        let uu____17316 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17316 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17363)::
                             (uu____17364,(arg,uu____17366))::[] ->
                             maybe_auto_squash arg
                         | (uu____17415,(arg,uu____17417))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17418)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17467)::uu____17468::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17519::(FStar_Pervasives_Native.Some (false
                                         ),uu____17520)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17571 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17585 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17585
                         then
                           let uu____17586 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17586 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17633)::uu____17634::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17685::(FStar_Pervasives_Native.Some (true
                                           ),uu____17686)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17737)::(uu____17738,(arg,uu____17740))::[]
                               -> maybe_auto_squash arg
                           | (uu____17789,(arg,uu____17791))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17792)::[]
                               -> maybe_auto_squash arg
                           | uu____17841 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17855 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17855
                            then
                              let uu____17856 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17856 with
                              | uu____17903::(FStar_Pervasives_Native.Some
                                              (true ),uu____17904)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17955)::uu____17956::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18007)::(uu____18008,(arg,uu____18010))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18059,(p,uu____18061))::(uu____18062,
                                                                (q,uu____18064))::[]
                                  ->
                                  let uu____18111 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18111
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18113 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18127 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18127
                               then
                                 let uu____18128 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18128 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18175)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18176)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18227)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18228)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18279)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18280)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18331)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18332)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18383,(arg,uu____18385))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18386)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18435)::(uu____18436,(arg,uu____18438))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18487,(arg,uu____18489))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18490)::[]
                                     ->
                                     let uu____18539 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18539
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18540)::(uu____18541,(arg,uu____18543))::[]
                                     ->
                                     let uu____18592 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18592
                                 | (uu____18593,(p,uu____18595))::(uu____18596,
                                                                   (q,uu____18598))::[]
                                     ->
                                     let uu____18645 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18645
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18647 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18661 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18661
                                  then
                                    let uu____18662 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18662 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18709)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18740)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18771 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18785 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18785
                                     then
                                       match args with
                                       | (t,uu____18787)::[] ->
                                           let uu____18804 =
                                             let uu____18805 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18805.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18804 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18808::[],body,uu____18810)
                                                ->
                                                let uu____18837 = simp_t body
                                                   in
                                                (match uu____18837 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18840 -> tm1)
                                            | uu____18843 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18845))::(t,uu____18847)::[]
                                           ->
                                           let uu____18886 =
                                             let uu____18887 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18887.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18886 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18890::[],body,uu____18892)
                                                ->
                                                let uu____18919 = simp_t body
                                                   in
                                                (match uu____18919 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18922 -> tm1)
                                            | uu____18925 -> tm1)
                                       | uu____18926 -> tm1
                                     else
                                       (let uu____18936 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18936
                                        then
                                          match args with
                                          | (t,uu____18938)::[] ->
                                              let uu____18955 =
                                                let uu____18956 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18956.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18955 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18959::[],body,uu____18961)
                                                   ->
                                                   let uu____18988 =
                                                     simp_t body  in
                                                   (match uu____18988 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18991 -> tm1)
                                               | uu____18994 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18996))::(t,uu____18998)::[]
                                              ->
                                              let uu____19037 =
                                                let uu____19038 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19038.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19037 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19041::[],body,uu____19043)
                                                   ->
                                                   let uu____19070 =
                                                     simp_t body  in
                                                   (match uu____19070 with
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
                                                    | uu____19073 -> tm1)
                                               | uu____19076 -> tm1)
                                          | uu____19077 -> tm1
                                        else
                                          (let uu____19087 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19087
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19088;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19089;_},uu____19090)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19107;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19108;_},uu____19109)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19126 -> tm1
                                           else
                                             (let uu____19136 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19136 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19156 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____19166;
                         FStar_Syntax_Syntax.vars = uu____19167;_},args)
                      ->
                      let uu____19189 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19189
                      then
                        let uu____19190 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19190 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19237)::
                             (uu____19238,(arg,uu____19240))::[] ->
                             maybe_auto_squash arg
                         | (uu____19289,(arg,uu____19291))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19292)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19341)::uu____19342::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19393::(FStar_Pervasives_Native.Some (false
                                         ),uu____19394)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19445 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19459 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19459
                         then
                           let uu____19460 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19460 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19507)::uu____19508::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19559::(FStar_Pervasives_Native.Some (true
                                           ),uu____19560)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19611)::(uu____19612,(arg,uu____19614))::[]
                               -> maybe_auto_squash arg
                           | (uu____19663,(arg,uu____19665))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19666)::[]
                               -> maybe_auto_squash arg
                           | uu____19715 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19729 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19729
                            then
                              let uu____19730 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19730 with
                              | uu____19777::(FStar_Pervasives_Native.Some
                                              (true ),uu____19778)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19829)::uu____19830::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19881)::(uu____19882,(arg,uu____19884))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19933,(p,uu____19935))::(uu____19936,
                                                                (q,uu____19938))::[]
                                  ->
                                  let uu____19985 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19985
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19987 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20001 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20001
                               then
                                 let uu____20002 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20002 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20049)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20050)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20101)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20102)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20153)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20154)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20205)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20206)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20257,(arg,uu____20259))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20260)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20309)::(uu____20310,(arg,uu____20312))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20361,(arg,uu____20363))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20364)::[]
                                     ->
                                     let uu____20413 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20413
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20414)::(uu____20415,(arg,uu____20417))::[]
                                     ->
                                     let uu____20466 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20466
                                 | (uu____20467,(p,uu____20469))::(uu____20470,
                                                                   (q,uu____20472))::[]
                                     ->
                                     let uu____20519 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20519
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20521 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20535 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20535
                                  then
                                    let uu____20536 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20536 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20583)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20614)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20645 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20659 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20659
                                     then
                                       match args with
                                       | (t,uu____20661)::[] ->
                                           let uu____20678 =
                                             let uu____20679 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20679.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20678 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20682::[],body,uu____20684)
                                                ->
                                                let uu____20711 = simp_t body
                                                   in
                                                (match uu____20711 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20714 -> tm1)
                                            | uu____20717 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20719))::(t,uu____20721)::[]
                                           ->
                                           let uu____20760 =
                                             let uu____20761 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20761.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20760 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20764::[],body,uu____20766)
                                                ->
                                                let uu____20793 = simp_t body
                                                   in
                                                (match uu____20793 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20796 -> tm1)
                                            | uu____20799 -> tm1)
                                       | uu____20800 -> tm1
                                     else
                                       (let uu____20810 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20810
                                        then
                                          match args with
                                          | (t,uu____20812)::[] ->
                                              let uu____20829 =
                                                let uu____20830 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20830.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20829 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20833::[],body,uu____20835)
                                                   ->
                                                   let uu____20862 =
                                                     simp_t body  in
                                                   (match uu____20862 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20865 -> tm1)
                                               | uu____20868 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20870))::(t,uu____20872)::[]
                                              ->
                                              let uu____20911 =
                                                let uu____20912 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20912.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20911 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20915::[],body,uu____20917)
                                                   ->
                                                   let uu____20944 =
                                                     simp_t body  in
                                                   (match uu____20944 with
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
                                                    | uu____20947 -> tm1)
                                               | uu____20950 -> tm1)
                                          | uu____20951 -> tm1
                                        else
                                          (let uu____20961 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20961
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20962;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20963;_},uu____20964)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20981;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20982;_},uu____20983)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21000 -> tm1
                                           else
                                             (let uu____21010 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____21010 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____21030 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____21045 = simp_t t  in
                      (match uu____21045 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____21048 ->
                      let uu____21071 = is_const_match tm1  in
                      (match uu____21071 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____21074 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____21084  ->
               (let uu____21086 = FStar_Syntax_Print.tag_of_term t  in
                let uu____21087 = FStar_Syntax_Print.term_to_string t  in
                let uu____21088 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____21095 =
                  let uu____21096 =
                    let uu____21099 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____21099
                     in
                  stack_to_string uu____21096  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____21086 uu____21087 uu____21088 uu____21095);
               (let uu____21122 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____21122
                then
                  let uu____21123 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____21123 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____21130 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____21131 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____21132 =
                          let uu____21133 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____21133
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____21130
                          uu____21131 uu____21132);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____21151 =
                     let uu____21152 =
                       let uu____21153 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____21153  in
                     FStar_Util.string_of_int uu____21152  in
                   let uu____21158 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____21159 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____21151 uu____21158 uu____21159)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____21165,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____21214  ->
                     let uu____21215 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____21215);
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
               let uu____21251 =
                 let uu___182_21252 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_21252.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_21252.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____21251
           | (Arg (Univ uu____21253,uu____21254,uu____21255))::uu____21256 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____21259,uu____21260))::uu____21261 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____21276,uu____21277),aq,r))::stack1
               when
               let uu____21327 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____21327 ->
               let t2 =
                 let uu____21331 =
                   let uu____21332 =
                     let uu____21333 = closure_as_term cfg env_arg tm  in
                     (uu____21333, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____21332  in
                 uu____21331 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____21339),aq,r))::stack1 ->
               (log cfg
                  (fun uu____21392  ->
                     let uu____21393 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____21393);
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
                  (let uu____21403 = FStar_ST.op_Bang m  in
                   match uu____21403 with
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
                   | FStar_Pervasives_Native.Some (uu____21540,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21587 =
                 log cfg
                   (fun uu____21591  ->
                      let uu____21592 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21592);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21596 =
                 let uu____21597 = FStar_Syntax_Subst.compress t1  in
                 uu____21597.FStar_Syntax_Syntax.n  in
               (match uu____21596 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21624 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21624  in
                    (log cfg
                       (fun uu____21628  ->
                          let uu____21629 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21629);
                     (let uu____21630 = FStar_List.tl stack  in
                      norm cfg env1 uu____21630 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21631);
                       FStar_Syntax_Syntax.pos = uu____21632;
                       FStar_Syntax_Syntax.vars = uu____21633;_},(e,uu____21635)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21664 when
                    (cfg.steps).primops ->
                    let uu____21679 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21679 with
                     | (hd1,args) ->
                         let uu____21716 =
                           let uu____21717 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21717.FStar_Syntax_Syntax.n  in
                         (match uu____21716 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21721 = find_prim_step cfg fv  in
                              (match uu____21721 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21724; arity = uu____21725;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21727;
                                     requires_binder_substitution =
                                       uu____21728;
                                     interpretation = uu____21729;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21742 -> fallback " (3)" ())
                          | uu____21745 -> fallback " (4)" ()))
                | uu____21746 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____21767  ->
                     let uu____21768 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21768);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21775 =
                   log cfg1
                     (fun uu____21780  ->
                        let uu____21781 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21782 =
                          let uu____21783 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21800  ->
                                    match uu____21800 with
                                    | (p,uu____21810,uu____21811) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21783
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21781 uu____21782);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_21828  ->
                                match uu___91_21828 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21829 -> false))
                         in
                      let steps =
                        let uu___183_21831 = cfg1.steps  in
                        {
                          beta = (uu___183_21831.beta);
                          iota = (uu___183_21831.iota);
                          zeta = false;
                          weak = (uu___183_21831.weak);
                          hnf = (uu___183_21831.hnf);
                          primops = (uu___183_21831.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_21831.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_21831.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_21831.pure_subterms_within_computations);
                          simplify = (uu___183_21831.simplify);
                          erase_universes = (uu___183_21831.erase_universes);
                          allow_unbound_universes =
                            (uu___183_21831.allow_unbound_universes);
                          reify_ = (uu___183_21831.reify_);
                          compress_uvars = (uu___183_21831.compress_uvars);
                          no_full_norm = (uu___183_21831.no_full_norm);
                          check_no_uvars = (uu___183_21831.check_no_uvars);
                          unmeta = (uu___183_21831.unmeta);
                          unascribe = (uu___183_21831.unascribe);
                          in_full_norm_request =
                            (uu___183_21831.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___183_21831.weakly_reduce_scrutinee)
                        }  in
                      let uu___184_21836 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_21836.tcenv);
                        debug = (uu___184_21836.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_21836.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_21836.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_21836.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21868 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21889 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21949  ->
                                    fun uu____21950  ->
                                      match (uu____21949, uu____21950) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____22041 = norm_pat env3 p1
                                             in
                                          (match uu____22041 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21889 with
                           | (pats1,env3) ->
                               ((let uu___185_22123 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_22123.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_22142 = x  in
                            let uu____22143 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_22142.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_22142.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22143
                            }  in
                          ((let uu___187_22157 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_22157.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_22168 = x  in
                            let uu____22169 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_22168.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_22168.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22169
                            }  in
                          ((let uu___189_22183 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_22183.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_22199 = x  in
                            let uu____22200 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_22199.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_22199.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22200
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_22207 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_22207.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____22217 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____22231 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____22231 with
                                  | (p,wopt,e) ->
                                      let uu____22251 = norm_pat env1 p  in
                                      (match uu____22251 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22276 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22276
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22283 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____22283
                      then
                        norm
                          (let uu___192_22286 = cfg1  in
                           {
                             steps =
                               (let uu___193_22289 = cfg1.steps  in
                                {
                                  beta = (uu___193_22289.beta);
                                  iota = (uu___193_22289.iota);
                                  zeta = (uu___193_22289.zeta);
                                  weak = (uu___193_22289.weak);
                                  hnf = (uu___193_22289.hnf);
                                  primops = (uu___193_22289.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___193_22289.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___193_22289.unfold_until);
                                  unfold_only = (uu___193_22289.unfold_only);
                                  unfold_fully =
                                    (uu___193_22289.unfold_fully);
                                  unfold_attr = (uu___193_22289.unfold_attr);
                                  unfold_tac = (uu___193_22289.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___193_22289.pure_subterms_within_computations);
                                  simplify = (uu___193_22289.simplify);
                                  erase_universes =
                                    (uu___193_22289.erase_universes);
                                  allow_unbound_universes =
                                    (uu___193_22289.allow_unbound_universes);
                                  reify_ = (uu___193_22289.reify_);
                                  compress_uvars =
                                    (uu___193_22289.compress_uvars);
                                  no_full_norm =
                                    (uu___193_22289.no_full_norm);
                                  check_no_uvars =
                                    (uu___193_22289.check_no_uvars);
                                  unmeta = (uu___193_22289.unmeta);
                                  unascribe = (uu___193_22289.unascribe);
                                  in_full_norm_request =
                                    (uu___193_22289.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___192_22286.tcenv);
                             debug = (uu___192_22286.debug);
                             delta_level = (uu___192_22286.delta_level);
                             primitive_steps =
                               (uu___192_22286.primitive_steps);
                             strong = (uu___192_22286.strong);
                             memoize_lazy = (uu___192_22286.memoize_lazy);
                             normalize_pure_lets =
                               (uu___192_22286.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22291 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22291)
                    in
                 let rec is_cons head1 =
                   let uu____22296 =
                     let uu____22297 = FStar_Syntax_Subst.compress head1  in
                     uu____22297.FStar_Syntax_Syntax.n  in
                   match uu____22296 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22301) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22306 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22307;
                         FStar_Syntax_Syntax.fv_delta = uu____22308;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22309;
                         FStar_Syntax_Syntax.fv_delta = uu____22310;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22311);_}
                       -> true
                   | uu____22318 -> false  in
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
                   let uu____22463 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____22463 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22550 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22589 ->
                                 let uu____22590 =
                                   let uu____22591 = is_cons head1  in
                                   Prims.op_Negation uu____22591  in
                                 FStar_Util.Inr uu____22590)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22616 =
                              let uu____22617 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22617.FStar_Syntax_Syntax.n  in
                            (match uu____22616 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22635 ->
                                 let uu____22636 =
                                   let uu____22637 = is_cons head1  in
                                   Prims.op_Negation uu____22637  in
                                 FStar_Util.Inr uu____22636))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22706)::rest_a,(p1,uu____22709)::rest_p) ->
                       let uu____22753 = matches_pat t2 p1  in
                       (match uu____22753 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22802 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22908 = matches_pat scrutinee1 p1  in
                       (match uu____22908 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____22948  ->
                                  let uu____22949 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22950 =
                                    let uu____22951 =
                                      FStar_List.map
                                        (fun uu____22961  ->
                                           match uu____22961 with
                                           | (uu____22966,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22951
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22949 uu____22950);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22998  ->
                                       match uu____22998 with
                                       | (bv,t2) ->
                                           let uu____23021 =
                                             let uu____23028 =
                                               let uu____23031 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____23031
                                                in
                                             let uu____23032 =
                                               let uu____23033 =
                                                 let uu____23064 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____23064, false)
                                                  in
                                               Clos uu____23033  in
                                             (uu____23028, uu____23032)  in
                                           uu____23021 :: env2) env1 s
                                 in
                              let uu____23181 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23181)))
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
    let uu____23204 =
      let uu____23207 = FStar_ST.op_Bang plugins  in p :: uu____23207  in
    FStar_ST.op_Colon_Equals plugins uu____23204  in
  let retrieve uu____23305 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____23370  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_23403  ->
                  match uu___92_23403 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____23407 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____23413 -> d  in
        let uu____23416 = to_fsteps s  in
        let uu____23417 =
          let uu____23418 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____23419 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____23420 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____23421 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____23422 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____23423 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____23418;
            primop = uu____23419;
            b380 = uu____23420;
            wpe = uu____23421;
            norm_delayed = uu____23422;
            print_normalized = uu____23423
          }  in
        let uu____23424 =
          let uu____23427 =
            let uu____23430 = retrieve_plugins ()  in
            FStar_List.append uu____23430 psteps  in
          add_steps built_in_primitive_steps uu____23427  in
        let uu____23433 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____23435 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____23435)
           in
        {
          steps = uu____23416;
          tcenv = e;
          debug = uu____23417;
          delta_level = d1;
          primitive_steps = uu____23424;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____23433
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
      fun t  -> let uu____23493 = config s e  in norm_comp uu____23493 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23506 = config [] env  in norm_universe uu____23506 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____23524 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23524  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23531 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___194_23550 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___194_23550.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___194_23550.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23557 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23557
          then
            let ct1 =
              let uu____23559 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23559 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23566 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23566
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___195_23570 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___195_23570.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___195_23570.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___195_23570.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___196_23572 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___196_23572.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___196_23572.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___196_23572.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___196_23572.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___197_23573 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___197_23573.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_23573.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23575 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____23587 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23587  in
      let uu____23594 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23594
      then
        let uu____23595 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23595 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23601  ->
                 let uu____23602 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23602)
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
            ((let uu____23619 =
                let uu____23624 =
                  let uu____23625 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23625
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23624)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23619);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23636 = config [AllowUnboundUniverses] env  in
          norm_comp uu____23636 [] c
        with
        | e ->
            ((let uu____23649 =
                let uu____23654 =
                  let uu____23655 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23655
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23654)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23649);
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
                   let uu____23692 =
                     let uu____23693 =
                       let uu____23700 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____23700)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23693  in
                   mk uu____23692 t01.FStar_Syntax_Syntax.pos
               | uu____23705 -> t2)
          | uu____23706 -> t2  in
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
        UnfoldUntil FStar_Syntax_Syntax.delta_constant;
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
        let uu____23746 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23746 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23775 ->
                 let uu____23782 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23782 with
                  | (actuals,uu____23792,uu____23793) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23807 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23807 with
                         | (binders,args) ->
                             let uu____23824 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23824
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
      | uu____23832 ->
          let uu____23833 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23833 with
           | (head1,args) ->
               let uu____23870 =
                 let uu____23871 = FStar_Syntax_Subst.compress head1  in
                 uu____23871.FStar_Syntax_Syntax.n  in
               (match uu____23870 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23874,thead) ->
                    let uu____23900 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23900 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23942 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___202_23950 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___202_23950.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___202_23950.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___202_23950.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___202_23950.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___202_23950.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___202_23950.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___202_23950.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___202_23950.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___202_23950.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___202_23950.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___202_23950.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___202_23950.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___202_23950.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___202_23950.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___202_23950.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___202_23950.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___202_23950.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___202_23950.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___202_23950.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___202_23950.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___202_23950.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___202_23950.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___202_23950.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___202_23950.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___202_23950.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___202_23950.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___202_23950.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___202_23950.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___202_23950.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___202_23950.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___202_23950.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___202_23950.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___202_23950.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___202_23950.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23942 with
                            | (uu____23951,ty,uu____23953) ->
                                eta_expand_with_type env t ty))
                | uu____23954 ->
                    let uu____23955 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___203_23963 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___203_23963.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___203_23963.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___203_23963.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___203_23963.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___203_23963.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___203_23963.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___203_23963.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___203_23963.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___203_23963.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___203_23963.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___203_23963.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___203_23963.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___203_23963.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___203_23963.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___203_23963.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___203_23963.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___203_23963.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___203_23963.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___203_23963.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___203_23963.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___203_23963.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___203_23963.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___203_23963.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___203_23963.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___203_23963.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___203_23963.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___203_23963.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___203_23963.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___203_23963.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___203_23963.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___203_23963.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___203_23963.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___203_23963.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___203_23963.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23955 with
                     | (uu____23964,ty,uu____23966) ->
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
      let uu___204_24023 = x  in
      let uu____24024 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___204_24023.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___204_24023.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____24024
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____24027 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____24052 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____24053 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____24054 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____24055 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____24062 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____24063 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____24064 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___205_24092 = rc  in
          let uu____24093 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____24100 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___205_24092.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____24093;
            FStar_Syntax_Syntax.residual_flags = uu____24100
          }  in
        let uu____24103 =
          let uu____24104 =
            let uu____24121 = elim_delayed_subst_binders bs  in
            let uu____24128 = elim_delayed_subst_term t2  in
            let uu____24129 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____24121, uu____24128, uu____24129)  in
          FStar_Syntax_Syntax.Tm_abs uu____24104  in
        mk1 uu____24103
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____24158 =
          let uu____24159 =
            let uu____24172 = elim_delayed_subst_binders bs  in
            let uu____24179 = elim_delayed_subst_comp c  in
            (uu____24172, uu____24179)  in
          FStar_Syntax_Syntax.Tm_arrow uu____24159  in
        mk1 uu____24158
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24192 =
          let uu____24193 =
            let uu____24200 = elim_bv bv  in
            let uu____24201 = elim_delayed_subst_term phi  in
            (uu____24200, uu____24201)  in
          FStar_Syntax_Syntax.Tm_refine uu____24193  in
        mk1 uu____24192
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24224 =
          let uu____24225 =
            let uu____24240 = elim_delayed_subst_term t2  in
            let uu____24241 = elim_delayed_subst_args args  in
            (uu____24240, uu____24241)  in
          FStar_Syntax_Syntax.Tm_app uu____24225  in
        mk1 uu____24224
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___206_24305 = p  in
              let uu____24306 =
                let uu____24307 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24307  in
              {
                FStar_Syntax_Syntax.v = uu____24306;
                FStar_Syntax_Syntax.p =
                  (uu___206_24305.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___207_24309 = p  in
              let uu____24310 =
                let uu____24311 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24311  in
              {
                FStar_Syntax_Syntax.v = uu____24310;
                FStar_Syntax_Syntax.p =
                  (uu___207_24309.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___208_24318 = p  in
              let uu____24319 =
                let uu____24320 =
                  let uu____24327 = elim_bv x  in
                  let uu____24328 = elim_delayed_subst_term t0  in
                  (uu____24327, uu____24328)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24320  in
              {
                FStar_Syntax_Syntax.v = uu____24319;
                FStar_Syntax_Syntax.p =
                  (uu___208_24318.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___209_24347 = p  in
              let uu____24348 =
                let uu____24349 =
                  let uu____24362 =
                    FStar_List.map
                      (fun uu____24385  ->
                         match uu____24385 with
                         | (x,b) ->
                             let uu____24398 = elim_pat x  in
                             (uu____24398, b)) pats
                     in
                  (fv, uu____24362)  in
                FStar_Syntax_Syntax.Pat_cons uu____24349  in
              {
                FStar_Syntax_Syntax.v = uu____24348;
                FStar_Syntax_Syntax.p =
                  (uu___209_24347.FStar_Syntax_Syntax.p)
              }
          | uu____24411 -> p  in
        let elim_branch uu____24433 =
          match uu____24433 with
          | (pat,wopt,t3) ->
              let uu____24459 = elim_pat pat  in
              let uu____24462 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24465 = elim_delayed_subst_term t3  in
              (uu____24459, uu____24462, uu____24465)
           in
        let uu____24470 =
          let uu____24471 =
            let uu____24494 = elim_delayed_subst_term t2  in
            let uu____24495 = FStar_List.map elim_branch branches  in
            (uu____24494, uu____24495)  in
          FStar_Syntax_Syntax.Tm_match uu____24471  in
        mk1 uu____24470
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24604 =
          match uu____24604 with
          | (tc,topt) ->
              let uu____24639 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24649 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24649
                | FStar_Util.Inr c ->
                    let uu____24651 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24651
                 in
              let uu____24652 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24639, uu____24652)
           in
        let uu____24661 =
          let uu____24662 =
            let uu____24689 = elim_delayed_subst_term t2  in
            let uu____24690 = elim_ascription a  in
            (uu____24689, uu____24690, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24662  in
        mk1 uu____24661
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___210_24735 = lb  in
          let uu____24736 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24739 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___210_24735.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___210_24735.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24736;
            FStar_Syntax_Syntax.lbeff =
              (uu___210_24735.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24739;
            FStar_Syntax_Syntax.lbattrs =
              (uu___210_24735.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___210_24735.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24742 =
          let uu____24743 =
            let uu____24756 =
              let uu____24763 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24763)  in
            let uu____24772 = elim_delayed_subst_term t2  in
            (uu____24756, uu____24772)  in
          FStar_Syntax_Syntax.Tm_let uu____24743  in
        mk1 uu____24742
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24805 =
          let uu____24806 =
            let uu____24823 = elim_delayed_subst_term t2  in
            (uv, uu____24823)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24806  in
        mk1 uu____24805
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24841 =
          let uu____24842 =
            let uu____24849 = elim_delayed_subst_term tm  in
            (uu____24849, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24842  in
        mk1 uu____24841
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24856 =
          let uu____24857 =
            let uu____24864 = elim_delayed_subst_term t2  in
            let uu____24865 = elim_delayed_subst_meta md  in
            (uu____24864, uu____24865)  in
          FStar_Syntax_Syntax.Tm_meta uu____24857  in
        mk1 uu____24856

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24872  ->
         match uu___93_24872 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24876 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24876
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
        let uu____24897 =
          let uu____24898 =
            let uu____24907 = elim_delayed_subst_term t  in
            (uu____24907, uopt)  in
          FStar_Syntax_Syntax.Total uu____24898  in
        mk1 uu____24897
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24920 =
          let uu____24921 =
            let uu____24930 = elim_delayed_subst_term t  in
            (uu____24930, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24921  in
        mk1 uu____24920
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___211_24935 = ct  in
          let uu____24936 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24939 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24948 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___211_24935.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___211_24935.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24936;
            FStar_Syntax_Syntax.effect_args = uu____24939;
            FStar_Syntax_Syntax.flags = uu____24948
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24951  ->
    match uu___94_24951 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24963 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24963
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24996 =
          let uu____25003 = elim_delayed_subst_term t  in (m, uu____25003)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24996
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____25011 =
          let uu____25020 = elim_delayed_subst_term t  in
          (m1, m2, uu____25020)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____25011
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____25043  ->
         match uu____25043 with
         | (t,q) ->
             let uu____25054 = elim_delayed_subst_term t  in (uu____25054, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____25074  ->
         match uu____25074 with
         | (x,q) ->
             let uu____25085 =
               let uu___212_25086 = x  in
               let uu____25087 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___212_25086.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___212_25086.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____25087
               }  in
             (uu____25085, q)) bs

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
            | (uu____25163,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25169,FStar_Util.Inl t) ->
                let uu____25175 =
                  let uu____25178 =
                    let uu____25179 =
                      let uu____25192 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25192)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25179  in
                  FStar_Syntax_Syntax.mk uu____25178  in
                uu____25175 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25196 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25196 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25224 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25279 ->
                    let uu____25280 =
                      let uu____25289 =
                        let uu____25290 = FStar_Syntax_Subst.compress t4  in
                        uu____25290.FStar_Syntax_Syntax.n  in
                      (uu____25289, tc)  in
                    (match uu____25280 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25315) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25352) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25391,FStar_Util.Inl uu____25392) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25415 -> failwith "Impossible")
                 in
              (match uu____25224 with
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
          let uu____25520 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25520 with
          | (univ_names1,binders1,tc) ->
              let uu____25578 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25578)
  
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
          let uu____25613 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25613 with
          | (univ_names1,binders1,tc) ->
              let uu____25673 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25673)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25706 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25706 with
           | (univ_names1,binders1,typ1) ->
               let uu___213_25734 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_25734.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_25734.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_25734.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_25734.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___214_25755 = s  in
          let uu____25756 =
            let uu____25757 =
              let uu____25766 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25766, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25757  in
          {
            FStar_Syntax_Syntax.sigel = uu____25756;
            FStar_Syntax_Syntax.sigrng =
              (uu___214_25755.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_25755.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_25755.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_25755.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25783 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25783 with
           | (univ_names1,uu____25801,typ1) ->
               let uu___215_25815 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_25815.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_25815.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_25815.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_25815.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25821 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25821 with
           | (univ_names1,uu____25839,typ1) ->
               let uu___216_25853 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_25853.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_25853.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_25853.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___216_25853.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25887 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25887 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25910 =
                            let uu____25911 =
                              let uu____25912 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25912  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25911
                             in
                          elim_delayed_subst_term uu____25910  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___217_25915 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___217_25915.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___217_25915.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___217_25915.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___217_25915.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___218_25916 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___218_25916.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___218_25916.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___218_25916.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___218_25916.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___219_25928 = s  in
          let uu____25929 =
            let uu____25930 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25930  in
          {
            FStar_Syntax_Syntax.sigel = uu____25929;
            FStar_Syntax_Syntax.sigrng =
              (uu___219_25928.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___219_25928.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___219_25928.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___219_25928.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25934 = elim_uvars_aux_t env us [] t  in
          (match uu____25934 with
           | (us1,uu____25952,t1) ->
               let uu___220_25966 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___220_25966.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___220_25966.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___220_25966.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___220_25966.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25967 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25969 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25969 with
           | (univs1,binders,signature) ->
               let uu____25997 =
                 let uu____26006 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26006 with
                 | (univs_opening,univs2) ->
                     let uu____26033 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26033)
                  in
               (match uu____25997 with
                | (univs_opening,univs_closing) ->
                    let uu____26050 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26056 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26057 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26056, uu____26057)  in
                    (match uu____26050 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26079 =
                           match uu____26079 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26097 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26097 with
                                | (us1,t1) ->
                                    let uu____26108 =
                                      let uu____26113 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26120 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26113, uu____26120)  in
                                    (match uu____26108 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26133 =
                                           let uu____26138 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26147 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26138, uu____26147)  in
                                         (match uu____26133 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26163 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26163
                                                 in
                                              let uu____26164 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26164 with
                                               | (uu____26185,uu____26186,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26201 =
                                                       let uu____26202 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26202
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26201
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26207 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26207 with
                           | (uu____26220,uu____26221,t1) -> t1  in
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
                             | uu____26281 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26298 =
                               let uu____26299 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26299.FStar_Syntax_Syntax.n  in
                             match uu____26298 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26358 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26387 =
                               let uu____26388 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26388.FStar_Syntax_Syntax.n  in
                             match uu____26387 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26409) ->
                                 let uu____26430 = destruct_action_body body
                                    in
                                 (match uu____26430 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26475 ->
                                 let uu____26476 = destruct_action_body t  in
                                 (match uu____26476 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26525 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26525 with
                           | (action_univs,t) ->
                               let uu____26534 = destruct_action_typ_templ t
                                  in
                               (match uu____26534 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___221_26575 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___221_26575.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___221_26575.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___222_26577 = ed  in
                           let uu____26578 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26579 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26580 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26581 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26582 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26583 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26584 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26585 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26586 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26587 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26588 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26589 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26590 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26591 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___222_26577.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___222_26577.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26578;
                             FStar_Syntax_Syntax.bind_wp = uu____26579;
                             FStar_Syntax_Syntax.if_then_else = uu____26580;
                             FStar_Syntax_Syntax.ite_wp = uu____26581;
                             FStar_Syntax_Syntax.stronger = uu____26582;
                             FStar_Syntax_Syntax.close_wp = uu____26583;
                             FStar_Syntax_Syntax.assert_p = uu____26584;
                             FStar_Syntax_Syntax.assume_p = uu____26585;
                             FStar_Syntax_Syntax.null_wp = uu____26586;
                             FStar_Syntax_Syntax.trivial = uu____26587;
                             FStar_Syntax_Syntax.repr = uu____26588;
                             FStar_Syntax_Syntax.return_repr = uu____26589;
                             FStar_Syntax_Syntax.bind_repr = uu____26590;
                             FStar_Syntax_Syntax.actions = uu____26591;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___222_26577.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___223_26594 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___223_26594.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___223_26594.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___223_26594.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___223_26594.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_26611 =
            match uu___95_26611 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26638 = elim_uvars_aux_t env us [] t  in
                (match uu____26638 with
                 | (us1,uu____26662,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___224_26681 = sub_eff  in
            let uu____26682 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26685 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___224_26681.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___224_26681.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26682;
              FStar_Syntax_Syntax.lift = uu____26685
            }  in
          let uu___225_26688 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___225_26688.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___225_26688.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___225_26688.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___225_26688.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26698 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26698 with
           | (univ_names1,binders1,comp1) ->
               let uu___226_26732 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___226_26732.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___226_26732.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___226_26732.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___226_26732.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26743 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26744 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  