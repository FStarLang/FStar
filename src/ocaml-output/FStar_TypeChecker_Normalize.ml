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
             let uu____2080 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2080 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2092 = FStar_Util.psmap_empty ()  in add_steps uu____2092 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2103 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2103
  
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
    match projectee with | Arg _0 -> true | uu____2249 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2285 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2321 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2392 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2440 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2496 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2538 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2576 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2612 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2628 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2653 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2653 with | (hd1,uu____2667) -> hd1
  
let mk :
  'Auu____2687 .
    'Auu____2687 ->
      FStar_Range.range -> 'Auu____2687 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2741 = FStar_ST.op_Bang r  in
          match uu____2741 with
          | FStar_Pervasives_Native.Some uu____2789 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____2857 =
      FStar_List.map
        (fun uu____2871  ->
           match uu____2871 with
           | (bopt,c) ->
               let uu____2884 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____2886 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____2884 uu____2886) env
       in
    FStar_All.pipe_right uu____2857 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_2889  ->
    match uu___79_2889 with
    | Clos (env,t,uu____2892,uu____2893) ->
        let uu____2938 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____2945 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____2938 uu____2945
    | Univ uu____2946 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2949  ->
    match uu___80_2949 with
    | Arg (c,uu____2951,uu____2952) ->
        let uu____2953 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2953
    | MemoLazy uu____2954 -> "MemoLazy"
    | Abs (uu____2961,bs,uu____2963,uu____2964,uu____2965) ->
        let uu____2970 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2970
    | UnivArgs uu____2975 -> "UnivArgs"
    | Match uu____2982 -> "Match"
    | App (uu____2991,t,uu____2993,uu____2994) ->
        let uu____2995 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2995
    | Meta (uu____2996,m,uu____2998) -> "Meta"
    | Let uu____2999 -> "Let"
    | Cfg uu____3008 -> "Cfg"
    | Debug (t,uu____3010) ->
        let uu____3011 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3011
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3019 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3019 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3050 . 'Auu____3050 Prims.list -> Prims.bool =
  fun uu___81_3056  ->
    match uu___81_3056 with | [] -> true | uu____3059 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3087 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3087
      with
      | uu____3106 ->
          let uu____3107 =
            let uu____3108 = FStar_Syntax_Print.db_to_string x  in
            let uu____3109 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3108
              uu____3109
             in
          failwith uu____3107
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3115 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3115
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3119 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3119
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3123 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3123
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
          let uu____3149 =
            FStar_List.fold_left
              (fun uu____3175  ->
                 fun u1  ->
                   match uu____3175 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3200 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3200 with
                        | (k_u,n1) ->
                            let uu____3215 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3215
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3149 with
          | (uu____3233,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3258 =
                   let uu____3259 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3259  in
                 match uu____3258 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3277 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3285 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3291 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3300 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3309 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3316 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3316 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3333 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3333 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3341 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3349 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3349 with
                                  | (uu____3354,m) -> n1 <= m))
                           in
                        if uu____3341 then rest1 else us1
                    | uu____3359 -> us1)
               | uu____3364 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3368 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3368
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3372 = aux u  in
           match uu____3372 with
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
            (fun uu____3476  ->
               let uu____3477 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3478 = env_to_string env  in
               let uu____3479 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3477 uu____3478 uu____3479);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3488 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3491 ->
                    let uu____3516 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3516
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3517 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3518 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3519 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3520 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3521 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3543 ->
                           let uu____3560 =
                             let uu____3561 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3562 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3561 uu____3562
                              in
                           failwith uu____3560
                       | uu____3565 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3571 =
                        let uu____3572 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3572  in
                      mk uu____3571 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3580 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3580  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3582 = lookup_bvar env x  in
                    (match uu____3582 with
                     | Univ uu____3585 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___125_3589 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___125_3589.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___125_3589.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3595,uu____3596) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3681  ->
                              fun stack1  ->
                                match uu____3681 with
                                | (a,aq) ->
                                    let uu____3693 =
                                      let uu____3694 =
                                        let uu____3701 =
                                          let uu____3702 =
                                            let uu____3733 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____3733, false)  in
                                          Clos uu____3702  in
                                        (uu____3701, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____3694  in
                                    uu____3693 :: stack1) args)
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
                    let uu____3927 = close_binders cfg env bs  in
                    (match uu____3927 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____3974 =
                      let uu____3985 =
                        let uu____3992 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____3992]  in
                      close_binders cfg env uu____3985  in
                    (match uu____3974 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4015 =
                             let uu____4016 =
                               let uu____4023 =
                                 let uu____4024 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4024
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4023, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4016  in
                           mk uu____4015 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4115 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4115
                      | FStar_Util.Inr c ->
                          let uu____4129 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4129
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4148 =
                        let uu____4149 =
                          let uu____4176 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4176, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4149  in
                      mk uu____4148 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4222 =
                            let uu____4223 =
                              let uu____4230 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4230, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4223  in
                          mk uu____4222 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4282  -> dummy :: env1) env
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
                    let uu____4303 =
                      let uu____4314 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4314
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4333 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___126_4349 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_4349.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_4349.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4333))
                       in
                    (match uu____4303 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___127_4367 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_4367.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_4367.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_4367.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_4367.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4381,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4440  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4465 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4465
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4485  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4509 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4509
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___128_4517 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4517.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4517.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___129_4518 = lb  in
                      let uu____4519 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___129_4518.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___129_4518.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4519;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___129_4518.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___129_4518.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4551  -> fun env1  -> dummy :: env1)
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
            (fun uu____4654  ->
               let uu____4655 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4656 = env_to_string env  in
               let uu____4657 = stack_to_string stack  in
               let uu____4658 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4655 uu____4656 uu____4657 uu____4658);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4663,uu____4664),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____4739 = close_binders cfg env' bs  in
               (match uu____4739 with
                | (bs1,uu____4753) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____4769 =
                      let uu___130_4770 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___130_4770.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___130_4770.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____4769)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____4812 =
                 match uu____4812 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____4883 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____4904 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____4964  ->
                                     fun uu____4965  ->
                                       match (uu____4964, uu____4965) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5056 = norm_pat env4 p1
                                              in
                                           (match uu____5056 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____4904 with
                            | (pats1,env4) ->
                                ((let uu___131_5138 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___131_5138.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___132_5157 = x  in
                             let uu____5158 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___132_5157.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___132_5157.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5158
                             }  in
                           ((let uu___133_5172 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___133_5172.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___134_5183 = x  in
                             let uu____5184 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5183.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5183.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5184
                             }  in
                           ((let uu___135_5198 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5198.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___136_5214 = x  in
                             let uu____5215 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5214.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5214.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5215
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___137_5224 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5224.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5229 = norm_pat env2 pat  in
                     (match uu____5229 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5274 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5274
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5293 =
                   let uu____5294 =
                     let uu____5317 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5317)  in
                   FStar_Syntax_Syntax.Tm_match uu____5294  in
                 mk uu____5293 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5412 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5501  ->
                                       match uu____5501 with
                                       | (a,q) ->
                                           let uu____5520 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5520, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5412
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5531 =
                       let uu____5538 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5538)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5531
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5550 =
                       let uu____5559 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5559)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5550
                 | uu____5564 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5568 -> failwith "Impossible: unexpected stack element")

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
        let uu____5582 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5631  ->
                  fun uu____5632  ->
                    match (uu____5631, uu____5632) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_5702 = b  in
                          let uu____5703 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_5702.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_5702.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5703
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5582 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5796 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5809 = inline_closure_env cfg env [] t  in
                 let uu____5810 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5809 uu____5810
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5823 = inline_closure_env cfg env [] t  in
                 let uu____5824 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5823 uu____5824
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5870  ->
                           match uu____5870 with
                           | (a,q) ->
                               let uu____5883 =
                                 inline_closure_env cfg env [] a  in
                               (uu____5883, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5898  ->
                           match uu___82_5898 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5902 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5902
                           | f -> f))
                    in
                 let uu____5906 =
                   let uu___139_5907 = c1  in
                   let uu____5908 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5908;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_5907.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5906)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5918  ->
            match uu___83_5918 with
            | FStar_Syntax_Syntax.DECREASES uu____5919 -> false
            | uu____5922 -> true))

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
                   (fun uu___84_5940  ->
                      match uu___84_5940 with
                      | FStar_Syntax_Syntax.DECREASES uu____5941 -> false
                      | uu____5944 -> true))
               in
            let rc1 =
              let uu___140_5946 = rc  in
              let uu____5947 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_5946.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5947;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5956 -> lopt

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
    let uu____6047 =
      let uu____6054 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6054  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6047  in
  let arg_as_bounded_int uu____6078 =
    match uu____6078 with
    | (a,uu____6090) ->
        let uu____6097 =
          let uu____6098 = FStar_Syntax_Subst.compress a  in
          uu____6098.FStar_Syntax_Syntax.n  in
        (match uu____6097 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6108;
                FStar_Syntax_Syntax.vars = uu____6109;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6111;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6112;_},uu____6113)::[])
             when
             let uu____6152 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6152 "int_to_t" ->
             let uu____6153 =
               let uu____6158 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6158)  in
             FStar_Pervasives_Native.Some uu____6153
         | uu____6163 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6203 = f a  in FStar_Pervasives_Native.Some uu____6203
    | uu____6204 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6252 = f a0 a1  in FStar_Pervasives_Native.Some uu____6252
    | uu____6253 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6295 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____6295)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____6344 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____6344)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____6371 =
    match uu____6371 with
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
                   let uu____6419 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____6419)) a407 a408)
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
                       let uu____6447 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6447)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6468 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6468)) a414 a415)
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
                       let uu____6496 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6496)) a417
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
                       let uu____6524 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6524)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6632 =
          let uu____6641 = as_a a  in
          let uu____6644 = as_b b  in (uu____6641, uu____6644)  in
        (match uu____6632 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6659 =
               let uu____6660 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6660  in
             FStar_Pervasives_Native.Some uu____6659
         | uu____6661 -> FStar_Pervasives_Native.None)
    | uu____6670 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6684 =
        let uu____6685 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6685  in
      mk uu____6684 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6695 =
      let uu____6698 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6698  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6695  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6730 =
      let uu____6731 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6731  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6730
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6749 = arg_as_string a1  in
        (match uu____6749 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6755 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6755 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6768 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6768
              | uu____6769 -> FStar_Pervasives_Native.None)
         | uu____6774 -> FStar_Pervasives_Native.None)
    | uu____6777 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6787 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6787
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6816 =
          let uu____6837 = arg_as_string fn  in
          let uu____6840 = arg_as_int from_line  in
          let uu____6843 = arg_as_int from_col  in
          let uu____6846 = arg_as_int to_line  in
          let uu____6849 = arg_as_int to_col  in
          (uu____6837, uu____6840, uu____6843, uu____6846, uu____6849)  in
        (match uu____6816 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6880 =
                 let uu____6881 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6882 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6881 uu____6882  in
               let uu____6883 =
                 let uu____6884 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6885 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6884 uu____6885  in
               FStar_Range.mk_range fn1 uu____6880 uu____6883  in
             let uu____6886 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6886
         | uu____6887 -> FStar_Pervasives_Native.None)
    | uu____6908 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6935)::(a1,uu____6937)::(a2,uu____6939)::[] ->
        let uu____6976 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6976 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6989 -> FStar_Pervasives_Native.None)
    | uu____6990 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7017)::[] ->
        let uu____7026 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7026 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7032 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7032
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7033 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7057 =
      let uu____7072 =
        let uu____7087 =
          let uu____7102 =
            let uu____7117 =
              let uu____7132 =
                let uu____7147 =
                  let uu____7162 =
                    let uu____7177 =
                      let uu____7192 =
                        let uu____7207 =
                          let uu____7222 =
                            let uu____7237 =
                              let uu____7252 =
                                let uu____7267 =
                                  let uu____7282 =
                                    let uu____7297 =
                                      let uu____7312 =
                                        let uu____7327 =
                                          let uu____7342 =
                                            let uu____7357 =
                                              let uu____7372 =
                                                let uu____7385 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7385,
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
                                              let uu____7392 =
                                                let uu____7407 =
                                                  let uu____7420 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7420,
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
                                                let uu____7427 =
                                                  let uu____7442 =
                                                    let uu____7457 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7457,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7466 =
                                                    let uu____7483 =
                                                      let uu____7498 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7498,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7483]  in
                                                  uu____7442 :: uu____7466
                                                   in
                                                uu____7407 :: uu____7427  in
                                              uu____7372 :: uu____7392  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7357
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7342
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
                                          :: uu____7327
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
                                        :: uu____7312
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
                                      :: uu____7297
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
                                                        let uu____7689 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7689 y)) a444
                                                a445 a446)))
                                    :: uu____7282
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7267
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7252
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7237
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7222
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7207
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7192
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
                                          let uu____7856 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7856)) a448 a449 a450)))
                      :: uu____7177
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
                                        let uu____7882 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7882)) a452 a453 a454)))
                    :: uu____7162
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
                                      let uu____7908 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7908)) a456 a457 a458)))
                  :: uu____7147
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
                                    let uu____7934 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7934)) a460 a461 a462)))
                :: uu____7132
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7117
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7102
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7087
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7072
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7057
     in
  let weak_ops =
    let uu____8073 =
      let uu____8092 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8092, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8073]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8176 =
        let uu____8177 =
          let uu____8178 = FStar_Syntax_Syntax.as_arg c  in [uu____8178]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8177  in
      uu____8176 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8228 =
                let uu____8241 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____8241, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8257  ->
                                    fun uu____8258  ->
                                      match (uu____8257, uu____8258) with
                                      | ((int_to_t1,x),(uu____8277,y)) ->
                                          let uu____8287 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8287)) a464 a465 a466)))
                 in
              let uu____8288 =
                let uu____8303 =
                  let uu____8316 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____8316, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8332  ->
                                      fun uu____8333  ->
                                        match (uu____8332, uu____8333) with
                                        | ((int_to_t1,x),(uu____8352,y)) ->
                                            let uu____8362 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8362)) a468 a469 a470)))
                   in
                let uu____8363 =
                  let uu____8378 =
                    let uu____8391 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____8391, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8407  ->
                                        fun uu____8408  ->
                                          match (uu____8407, uu____8408) with
                                          | ((int_to_t1,x),(uu____8427,y)) ->
                                              let uu____8437 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8437)) a472 a473 a474)))
                     in
                  let uu____8438 =
                    let uu____8453 =
                      let uu____8466 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8466, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8478  ->
                                        match uu____8478 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____8453]  in
                  uu____8378 :: uu____8438  in
                uu____8303 :: uu____8363  in
              uu____8228 :: uu____8288))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8592 =
                let uu____8605 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8605, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8621  ->
                                    fun uu____8622  ->
                                      match (uu____8621, uu____8622) with
                                      | ((int_to_t1,x),(uu____8641,y)) ->
                                          let uu____8651 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8651)) a479 a480 a481)))
                 in
              let uu____8652 =
                let uu____8667 =
                  let uu____8680 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8680, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8696  ->
                                      fun uu____8697  ->
                                        match (uu____8696, uu____8697) with
                                        | ((int_to_t1,x),(uu____8716,y)) ->
                                            let uu____8726 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8726)) a483 a484 a485)))
                   in
                [uu____8667]  in
              uu____8592 :: uu____8652))
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
    | (_typ,uu____8838)::(a1,uu____8840)::(a2,uu____8842)::[] ->
        let uu____8879 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8879 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8885 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8885.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8885.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_8889 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_8889.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_8889.FStar_Syntax_Syntax.vars)
                })
         | uu____8890 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8892)::uu____8893::(a1,uu____8895)::(a2,uu____8897)::[] ->
        let uu____8946 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8946 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8952 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8952.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8952.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_8956 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_8956.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_8956.FStar_Syntax_Syntax.vars)
                })
         | uu____8957 -> FStar_Pervasives_Native.None)
    | uu____8958 -> failwith "Unexpected number of arguments"  in
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
    let uu____9010 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9010 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9055 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9055) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9115  ->
           fun subst1  ->
             match uu____9115 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9156,uu____9157)) ->
                      let uu____9216 = b  in
                      (match uu____9216 with
                       | (bv,uu____9224) ->
                           let uu____9225 =
                             let uu____9226 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____9226  in
                           if uu____9225
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____9231 = unembed_binder term1  in
                              match uu____9231 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____9238 =
                                      let uu___143_9239 = bv  in
                                      let uu____9240 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_9239.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_9239.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____9240
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____9238
                                     in
                                  let b_for_x =
                                    let uu____9244 =
                                      let uu____9251 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____9251)
                                       in
                                    FStar_Syntax_Syntax.NT uu____9244  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_9261  ->
                                         match uu___85_9261 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____9262,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9264;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9265;_})
                                             ->
                                             let uu____9270 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____9270
                                         | uu____9271 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____9272 -> subst1)) env []
  
let reduce_primops :
  'Auu____9289 'Auu____9290 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9289) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9290 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____9332 = FStar_Syntax_Util.head_and_args tm  in
             match uu____9332 with
             | (head1,args) ->
                 let uu____9369 =
                   let uu____9370 = FStar_Syntax_Util.un_uinst head1  in
                   uu____9370.FStar_Syntax_Syntax.n  in
                 (match uu____9369 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____9374 = find_prim_step cfg fv  in
                      (match uu____9374 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____9396  ->
                                   let uu____9397 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____9398 =
                                     FStar_Util.string_of_int l  in
                                   let uu____9405 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____9397 uu____9398 uu____9405);
                              tm)
                           else
                             (let uu____9407 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____9407 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9518  ->
                                        let uu____9519 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9519);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9522  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9524 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9524 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9530  ->
                                              let uu____9531 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9531);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9537  ->
                                              let uu____9538 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9539 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9538 uu____9539);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9540 ->
                           (log_primops cfg
                              (fun uu____9544  ->
                                 let uu____9545 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9545);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9549  ->
                            let uu____9550 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9550);
                       (match args with
                        | (a1,uu____9552)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9569 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9581  ->
                            let uu____9582 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9582);
                       (match args with
                        | (t,uu____9584)::(r,uu____9586)::[] ->
                            let uu____9613 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____9613 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___144_9617 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___144_9617.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___144_9617.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9620 -> tm))
                  | uu____9629 -> tm))
  
let reduce_equality :
  'Auu____9634 'Auu____9635 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9634) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9635 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_9673 = cfg  in
         {
           steps =
             (let uu___146_9676 = default_steps  in
              {
                beta = (uu___146_9676.beta);
                iota = (uu___146_9676.iota);
                zeta = (uu___146_9676.zeta);
                weak = (uu___146_9676.weak);
                hnf = (uu___146_9676.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_9676.do_not_unfold_pure_lets);
                unfold_until = (uu___146_9676.unfold_until);
                unfold_only = (uu___146_9676.unfold_only);
                unfold_fully = (uu___146_9676.unfold_fully);
                unfold_attr = (uu___146_9676.unfold_attr);
                unfold_tac = (uu___146_9676.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_9676.pure_subterms_within_computations);
                simplify = (uu___146_9676.simplify);
                erase_universes = (uu___146_9676.erase_universes);
                allow_unbound_universes =
                  (uu___146_9676.allow_unbound_universes);
                reify_ = (uu___146_9676.reify_);
                compress_uvars = (uu___146_9676.compress_uvars);
                no_full_norm = (uu___146_9676.no_full_norm);
                check_no_uvars = (uu___146_9676.check_no_uvars);
                unmeta = (uu___146_9676.unmeta);
                unascribe = (uu___146_9676.unascribe);
                in_full_norm_request = (uu___146_9676.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___146_9676.weakly_reduce_scrutinee)
              });
           tcenv = (uu___145_9673.tcenv);
           debug = (uu___145_9673.debug);
           delta_level = (uu___145_9673.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_9673.strong);
           memoize_lazy = (uu___145_9673.memoize_lazy);
           normalize_pure_lets = (uu___145_9673.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9680 .
    FStar_Syntax_Syntax.term -> 'Auu____9680 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9693 =
        let uu____9700 =
          let uu____9701 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9701.FStar_Syntax_Syntax.n  in
        (uu____9700, args)  in
      match uu____9693 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9707::uu____9708::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9712::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9717::uu____9718::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9721 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9732  ->
    match uu___86_9732 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9738 =
          let uu____9741 =
            let uu____9742 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9742  in
          [uu____9741]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9738
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9748 =
          let uu____9751 =
            let uu____9752 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9752  in
          [uu____9751]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9748
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9768 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9768) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9810 =
          let uu____9815 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9815 s  in
        match uu____9810 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9831 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9831
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9848::(tm,uu____9850)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9879)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9900)::uu____9901::(tm,uu____9903)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9940 =
            let uu____9945 = full_norm steps  in parse_steps uu____9945  in
          (match uu____9940 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9984 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_10001  ->
    match uu___87_10001 with
    | (App
        (uu____10004,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10005;
                       FStar_Syntax_Syntax.vars = uu____10006;_},uu____10007,uu____10008))::uu____10009
        -> true
    | uu____10016 -> false
  
let firstn :
  'Auu____10022 .
    Prims.int ->
      'Auu____10022 Prims.list ->
        ('Auu____10022 Prims.list,'Auu____10022 Prims.list)
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
          (uu____10058,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10059;
                         FStar_Syntax_Syntax.vars = uu____10060;_},uu____10061,uu____10062))::uu____10063
          -> (cfg.steps).reify_
      | uu____10070 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10089) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10099) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____10118  ->
                  match uu____10118 with
                  | (a,uu____10126) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10132 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____10157 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____10158 -> false
    | FStar_Syntax_Syntax.Tm_type uu____10175 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____10176 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____10177 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____10178 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____10179 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____10180 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____10187 -> false
    | FStar_Syntax_Syntax.Tm_let uu____10194 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____10207 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____10224 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____10237 -> true
    | FStar_Syntax_Syntax.Tm_match uu____10244 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____10306  ->
                   match uu____10306 with
                   | (a,uu____10314) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____10321) ->
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
                     (fun uu____10443  ->
                        match uu____10443 with
                        | (a,uu____10451) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____10456,uu____10457,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____10463,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____10469 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____10476 -> false
            | FStar_Syntax_Syntax.Meta_named uu____10477 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10659 ->
                   let uu____10684 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10684
               | uu____10685 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____10693  ->
               let uu____10694 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10695 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10696 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10703 =
                 let uu____10704 =
                   let uu____10707 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10707
                    in
                 stack_to_string uu____10704  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10694 uu____10695 uu____10696 uu____10703);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10730 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10731 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____10732 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10733;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10734;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10737;
                 FStar_Syntax_Syntax.fv_delta = uu____10738;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10739;
                 FStar_Syntax_Syntax.fv_delta = uu____10740;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10741);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____10748 ->
               let uu____10755 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____10755
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10785 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10785)
               ->
               let cfg' =
                 let uu___147_10787 = cfg  in
                 {
                   steps =
                     (let uu___148_10790 = cfg.steps  in
                      {
                        beta = (uu___148_10790.beta);
                        iota = (uu___148_10790.iota);
                        zeta = (uu___148_10790.zeta);
                        weak = (uu___148_10790.weak);
                        hnf = (uu___148_10790.hnf);
                        primops = (uu___148_10790.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_10790.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_10790.unfold_attr);
                        unfold_tac = (uu___148_10790.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_10790.pure_subterms_within_computations);
                        simplify = (uu___148_10790.simplify);
                        erase_universes = (uu___148_10790.erase_universes);
                        allow_unbound_universes =
                          (uu___148_10790.allow_unbound_universes);
                        reify_ = (uu___148_10790.reify_);
                        compress_uvars = (uu___148_10790.compress_uvars);
                        no_full_norm = (uu___148_10790.no_full_norm);
                        check_no_uvars = (uu___148_10790.check_no_uvars);
                        unmeta = (uu___148_10790.unmeta);
                        unascribe = (uu___148_10790.unascribe);
                        in_full_norm_request =
                          (uu___148_10790.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___148_10790.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___147_10787.tcenv);
                   debug = (uu___147_10787.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_10787.primitive_steps);
                   strong = (uu___147_10787.strong);
                   memoize_lazy = (uu___147_10787.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10795 = get_norm_request (norm cfg' env []) args  in
               (match uu____10795 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10826  ->
                              fun stack1  ->
                                match uu____10826 with
                                | (a,aq) ->
                                    let uu____10838 =
                                      let uu____10839 =
                                        let uu____10846 =
                                          let uu____10847 =
                                            let uu____10878 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10878, false)  in
                                          Clos uu____10847  in
                                        (uu____10846, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10839  in
                                    uu____10838 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10962  ->
                          let uu____10963 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10963);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10985 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10990  ->
                                match uu___88_10990 with
                                | UnfoldUntil uu____10991 -> true
                                | UnfoldOnly uu____10992 -> true
                                | UnfoldFully uu____10995 -> true
                                | uu____10998 -> false))
                         in
                      if uu____10985
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_11003 = cfg  in
                      let uu____11004 =
                        let uu___150_11005 = to_fsteps s  in
                        {
                          beta = (uu___150_11005.beta);
                          iota = (uu___150_11005.iota);
                          zeta = (uu___150_11005.zeta);
                          weak = (uu___150_11005.weak);
                          hnf = (uu___150_11005.hnf);
                          primops = (uu___150_11005.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_11005.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_11005.unfold_until);
                          unfold_only = (uu___150_11005.unfold_only);
                          unfold_fully = (uu___150_11005.unfold_fully);
                          unfold_attr = (uu___150_11005.unfold_attr);
                          unfold_tac = (uu___150_11005.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_11005.pure_subterms_within_computations);
                          simplify = (uu___150_11005.simplify);
                          erase_universes = (uu___150_11005.erase_universes);
                          allow_unbound_universes =
                            (uu___150_11005.allow_unbound_universes);
                          reify_ = (uu___150_11005.reify_);
                          compress_uvars = (uu___150_11005.compress_uvars);
                          no_full_norm = (uu___150_11005.no_full_norm);
                          check_no_uvars = (uu___150_11005.check_no_uvars);
                          unmeta = (uu___150_11005.unmeta);
                          unascribe = (uu___150_11005.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___150_11005.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____11004;
                        tcenv = (uu___149_11003.tcenv);
                        debug = (uu___149_11003.debug);
                        delta_level;
                        primitive_steps = (uu___149_11003.primitive_steps);
                        strong = (uu___149_11003.strong);
                        memoize_lazy = (uu___149_11003.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____11014 =
                          let uu____11015 =
                            let uu____11020 = FStar_Util.now ()  in
                            (t1, uu____11020)  in
                          Debug uu____11015  in
                        uu____11014 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11024 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11024
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11033 =
                      let uu____11040 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11040, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11033  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____11050 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____11050  in
               let uu____11051 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____11051
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____11057  ->
                       let uu____11058 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11059 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____11058 uu____11059);
                  if b
                  then
                    (let uu____11060 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____11060 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____11068 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____11068) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____11081),uu____11082);
                                FStar_Syntax_Syntax.sigrng = uu____11083;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____11085;
                                FStar_Syntax_Syntax.sigattrs = uu____11086;_},uu____11087),uu____11088)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____11153 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_11157  ->
                               match uu___89_11157 with
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
                          (let uu____11167 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____11167))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____11186) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____11221,uu____11222) -> false)))
                     in
                  let uu____11239 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____11255 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____11255 then (true, true) else (false, false)
                     in
                  match uu____11239 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____11268  ->
                            let uu____11269 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____11270 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____11271 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____11269 uu____11270 uu____11271);
                       if should_delta2
                       then
                         (let uu____11272 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_11288 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_11291 = cfg.steps  in
                                      {
                                        beta = (uu___152_11291.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_11291.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_11291.unfold_attr);
                                        unfold_tac =
                                          (uu___152_11291.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_11291.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_11291.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_11291.allow_unbound_universes);
                                        reify_ = (uu___152_11291.reify_);
                                        compress_uvars =
                                          (uu___152_11291.compress_uvars);
                                        no_full_norm =
                                          (uu___152_11291.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_11291.check_no_uvars);
                                        unmeta = (uu___152_11291.unmeta);
                                        unascribe =
                                          (uu___152_11291.unascribe);
                                        in_full_norm_request =
                                          (uu___152_11291.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___152_11291.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___151_11288.tcenv);
                                   debug = (uu___151_11288.debug);
                                   delta_level = (uu___151_11288.delta_level);
                                   primitive_steps =
                                     (uu___151_11288.primitive_steps);
                                   strong = (uu___151_11288.strong);
                                   memoize_lazy =
                                     (uu___151_11288.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_11288.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____11272 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11305 = lookup_bvar env x  in
               (match uu____11305 with
                | Univ uu____11306 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____11355 = FStar_ST.op_Bang r  in
                      (match uu____11355 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11473  ->
                                 let uu____11474 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11475 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11474
                                   uu____11475);
                            (let uu____11476 = maybe_weakly_reduced t'  in
                             if uu____11476
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____11477 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11548)::uu____11549 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11558)::uu____11559 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11571,uu____11572))::stack_rest ->
                    (match c with
                     | Univ uu____11576 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11585 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11606  ->
                                    let uu____11607 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11607);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11647  ->
                                    let uu____11648 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11648);
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
                       (fun uu____11726  ->
                          let uu____11727 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11727);
                     norm cfg env stack1 t1)
                | (Debug uu____11728)::uu____11729 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11739 = cfg.steps  in
                             {
                               beta = (uu___153_11739.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11739.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11739.unfold_until);
                               unfold_only = (uu___153_11739.unfold_only);
                               unfold_fully = (uu___153_11739.unfold_fully);
                               unfold_attr = (uu___153_11739.unfold_attr);
                               unfold_tac = (uu___153_11739.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11739.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11739.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11739.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11739.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11739.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_11739.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_11741 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11741.tcenv);
                               debug = (uu___154_11741.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11741.primitive_steps);
                               strong = (uu___154_11741.strong);
                               memoize_lazy = (uu___154_11741.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11741.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11743 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11743 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11785  -> dummy :: env1) env)
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
                                          let uu____11822 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11822)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11827 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11827.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11827.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11828 -> lopt  in
                           (log cfg
                              (fun uu____11834  ->
                                 let uu____11835 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11835);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11844 = cfg  in
                               {
                                 steps = (uu___156_11844.steps);
                                 tcenv = (uu___156_11844.tcenv);
                                 debug = (uu___156_11844.debug);
                                 delta_level = (uu___156_11844.delta_level);
                                 primitive_steps =
                                   (uu___156_11844.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11844.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11844.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11855)::uu____11856 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11868 = cfg.steps  in
                             {
                               beta = (uu___153_11868.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11868.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11868.unfold_until);
                               unfold_only = (uu___153_11868.unfold_only);
                               unfold_fully = (uu___153_11868.unfold_fully);
                               unfold_attr = (uu___153_11868.unfold_attr);
                               unfold_tac = (uu___153_11868.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11868.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11868.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11868.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11868.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11868.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_11868.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_11870 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_11870.tcenv);
                               debug = (uu___154_11870.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_11870.primitive_steps);
                               strong = (uu___154_11870.strong);
                               memoize_lazy = (uu___154_11870.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_11870.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____11872 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11872 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11914  -> dummy :: env1) env)
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
                                          let uu____11951 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11951)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_11956 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_11956.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_11956.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11957 -> lopt  in
                           (log cfg
                              (fun uu____11963  ->
                                 let uu____11964 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11964);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_11973 = cfg  in
                               {
                                 steps = (uu___156_11973.steps);
                                 tcenv = (uu___156_11973.tcenv);
                                 debug = (uu___156_11973.debug);
                                 delta_level = (uu___156_11973.delta_level);
                                 primitive_steps =
                                   (uu___156_11973.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_11973.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_11973.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11984)::uu____11985 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_11999 = cfg.steps  in
                             {
                               beta = (uu___153_11999.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_11999.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_11999.unfold_until);
                               unfold_only = (uu___153_11999.unfold_only);
                               unfold_fully = (uu___153_11999.unfold_fully);
                               unfold_attr = (uu___153_11999.unfold_attr);
                               unfold_tac = (uu___153_11999.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_11999.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_11999.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_11999.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_11999.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_11999.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_11999.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12001 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12001.tcenv);
                               debug = (uu___154_12001.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12001.primitive_steps);
                               strong = (uu___154_12001.strong);
                               memoize_lazy = (uu___154_12001.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12001.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12003 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12003 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12045  -> dummy :: env1) env)
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
                                          let uu____12082 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12082)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12087 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12087.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12087.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12088 -> lopt  in
                           (log cfg
                              (fun uu____12094  ->
                                 let uu____12095 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12095);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12104 = cfg  in
                               {
                                 steps = (uu___156_12104.steps);
                                 tcenv = (uu___156_12104.tcenv);
                                 debug = (uu___156_12104.debug);
                                 delta_level = (uu___156_12104.delta_level);
                                 primitive_steps =
                                   (uu___156_12104.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12104.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12104.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12115)::uu____12116 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12130 = cfg.steps  in
                             {
                               beta = (uu___153_12130.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12130.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12130.unfold_until);
                               unfold_only = (uu___153_12130.unfold_only);
                               unfold_fully = (uu___153_12130.unfold_fully);
                               unfold_attr = (uu___153_12130.unfold_attr);
                               unfold_tac = (uu___153_12130.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12130.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12130.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12130.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12130.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12130.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12130.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12132 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12132.tcenv);
                               debug = (uu___154_12132.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12132.primitive_steps);
                               strong = (uu___154_12132.strong);
                               memoize_lazy = (uu___154_12132.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12132.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12134 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12134 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12176  -> dummy :: env1) env)
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
                                          let uu____12213 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12213)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12218 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12218.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12218.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12219 -> lopt  in
                           (log cfg
                              (fun uu____12225  ->
                                 let uu____12226 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12226);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12235 = cfg  in
                               {
                                 steps = (uu___156_12235.steps);
                                 tcenv = (uu___156_12235.tcenv);
                                 debug = (uu___156_12235.debug);
                                 delta_level = (uu___156_12235.delta_level);
                                 primitive_steps =
                                   (uu___156_12235.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12235.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12235.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12246)::uu____12247 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12265 = cfg.steps  in
                             {
                               beta = (uu___153_12265.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12265.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12265.unfold_until);
                               unfold_only = (uu___153_12265.unfold_only);
                               unfold_fully = (uu___153_12265.unfold_fully);
                               unfold_attr = (uu___153_12265.unfold_attr);
                               unfold_tac = (uu___153_12265.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12265.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12265.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12265.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12265.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12265.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12265.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12267 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12267.tcenv);
                               debug = (uu___154_12267.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12267.primitive_steps);
                               strong = (uu___154_12267.strong);
                               memoize_lazy = (uu___154_12267.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12267.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12269 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12269 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12311  -> dummy :: env1) env)
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
                                          let uu____12348 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12348)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12353 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12353.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12353.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12354 -> lopt  in
                           (log cfg
                              (fun uu____12360  ->
                                 let uu____12361 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12361);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12370 = cfg  in
                               {
                                 steps = (uu___156_12370.steps);
                                 tcenv = (uu___156_12370.tcenv);
                                 debug = (uu___156_12370.debug);
                                 delta_level = (uu___156_12370.delta_level);
                                 primitive_steps =
                                   (uu___156_12370.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12370.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12370.normalize_pure_lets)
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
                             let uu___153_12384 = cfg.steps  in
                             {
                               beta = (uu___153_12384.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12384.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12384.unfold_until);
                               unfold_only = (uu___153_12384.unfold_only);
                               unfold_fully = (uu___153_12384.unfold_fully);
                               unfold_attr = (uu___153_12384.unfold_attr);
                               unfold_tac = (uu___153_12384.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12384.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12384.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12384.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12384.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12384.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12384.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12386 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12386.tcenv);
                               debug = (uu___154_12386.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12386.primitive_steps);
                               strong = (uu___154_12386.strong);
                               memoize_lazy = (uu___154_12386.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12386.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12388 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12388 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12430  -> dummy :: env1) env)
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
                                          let uu____12467 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12467)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12472 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12472.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12472.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12473 -> lopt  in
                           (log cfg
                              (fun uu____12479  ->
                                 let uu____12480 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12480);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12489 = cfg  in
                               {
                                 steps = (uu___156_12489.steps);
                                 tcenv = (uu___156_12489.tcenv);
                                 debug = (uu___156_12489.debug);
                                 delta_level = (uu___156_12489.delta_level);
                                 primitive_steps =
                                   (uu___156_12489.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12489.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12489.normalize_pure_lets)
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
                      (fun uu____12538  ->
                         fun stack1  ->
                           match uu____12538 with
                           | (a,aq) ->
                               let uu____12550 =
                                 let uu____12551 =
                                   let uu____12558 =
                                     let uu____12559 =
                                       let uu____12590 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12590, false)  in
                                     Clos uu____12559  in
                                   (uu____12558, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12551  in
                               uu____12550 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12674  ->
                     let uu____12675 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12675);
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
                             ((let uu___157_12711 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12711.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12711.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12712 ->
                      let uu____12717 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12717)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12720 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12720 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12751 =
                          let uu____12752 =
                            let uu____12759 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_12761 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_12761.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_12761.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12759)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12752  in
                        mk uu____12751 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12780 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12780
               else
                 (let uu____12782 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12782 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12790 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12814  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12790 c1  in
                      let t2 =
                        let uu____12836 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12836 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12947)::uu____12948 ->
                    (log cfg
                       (fun uu____12961  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12962)::uu____12963 ->
                    (log cfg
                       (fun uu____12974  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12975,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12976;
                                   FStar_Syntax_Syntax.vars = uu____12977;_},uu____12978,uu____12979))::uu____12980
                    ->
                    (log cfg
                       (fun uu____12989  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12990)::uu____12991 ->
                    (log cfg
                       (fun uu____13002  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13003 ->
                    (log cfg
                       (fun uu____13006  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13010  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13027 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13027
                         | FStar_Util.Inr c ->
                             let uu____13035 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13035
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13048 =
                               let uu____13049 =
                                 let uu____13076 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13076, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13049
                                in
                             mk uu____13048 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____13095 ->
                           let uu____13096 =
                             let uu____13097 =
                               let uu____13098 =
                                 let uu____13125 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13125, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13098
                                in
                             mk uu____13097 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____13096))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___159_13202 = cfg  in
                   {
                     steps =
                       (let uu___160_13205 = cfg.steps  in
                        {
                          beta = (uu___160_13205.beta);
                          iota = (uu___160_13205.iota);
                          zeta = (uu___160_13205.zeta);
                          weak = true;
                          hnf = (uu___160_13205.hnf);
                          primops = (uu___160_13205.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_13205.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_13205.unfold_until);
                          unfold_only = (uu___160_13205.unfold_only);
                          unfold_fully = (uu___160_13205.unfold_fully);
                          unfold_attr = (uu___160_13205.unfold_attr);
                          unfold_tac = (uu___160_13205.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_13205.pure_subterms_within_computations);
                          simplify = (uu___160_13205.simplify);
                          erase_universes = (uu___160_13205.erase_universes);
                          allow_unbound_universes =
                            (uu___160_13205.allow_unbound_universes);
                          reify_ = (uu___160_13205.reify_);
                          compress_uvars = (uu___160_13205.compress_uvars);
                          no_full_norm = (uu___160_13205.no_full_norm);
                          check_no_uvars = (uu___160_13205.check_no_uvars);
                          unmeta = (uu___160_13205.unmeta);
                          unascribe = (uu___160_13205.unascribe);
                          in_full_norm_request =
                            (uu___160_13205.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___160_13205.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___159_13202.tcenv);
                     debug = (uu___159_13202.debug);
                     delta_level = (uu___159_13202.delta_level);
                     primitive_steps = (uu___159_13202.primitive_steps);
                     strong = (uu___159_13202.strong);
                     memoize_lazy = (uu___159_13202.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_13202.normalize_pure_lets)
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
                         let uu____13241 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13241 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_13261 = cfg  in
                               let uu____13262 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_13261.steps);
                                 tcenv = uu____13262;
                                 debug = (uu___161_13261.debug);
                                 delta_level = (uu___161_13261.delta_level);
                                 primitive_steps =
                                   (uu___161_13261.primitive_steps);
                                 strong = (uu___161_13261.strong);
                                 memoize_lazy = (uu___161_13261.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_13261.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____13267 =
                                 let uu____13268 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13268  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13267
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_13271 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_13271.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_13271.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_13271.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_13271.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____13272 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13272
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13283,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13284;
                               FStar_Syntax_Syntax.lbunivs = uu____13285;
                               FStar_Syntax_Syntax.lbtyp = uu____13286;
                               FStar_Syntax_Syntax.lbeff = uu____13287;
                               FStar_Syntax_Syntax.lbdef = uu____13288;
                               FStar_Syntax_Syntax.lbattrs = uu____13289;
                               FStar_Syntax_Syntax.lbpos = uu____13290;_}::uu____13291),uu____13292)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13332 =
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
               if uu____13332
               then
                 let binder =
                   let uu____13334 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13334  in
                 let env1 =
                   let uu____13344 =
                     let uu____13351 =
                       let uu____13352 =
                         let uu____13383 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13383,
                           false)
                          in
                       Clos uu____13352  in
                     ((FStar_Pervasives_Native.Some binder), uu____13351)  in
                   uu____13344 :: env  in
                 (log cfg
                    (fun uu____13476  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____13480  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13481 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13481))
                 else
                   (let uu____13483 =
                      let uu____13488 =
                        let uu____13489 =
                          let uu____13490 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____13490
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____13489]  in
                      FStar_Syntax_Subst.open_term uu____13488 body  in
                    match uu____13483 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13499  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____13507 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____13507  in
                            FStar_Util.Inl
                              (let uu___163_13517 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_13517.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_13517.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____13520  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_13522 = lb  in
                             let uu____13523 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_13522.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_13522.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13523;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_13522.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_13522.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13558  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_13581 = cfg  in
                             {
                               steps = (uu___165_13581.steps);
                               tcenv = (uu___165_13581.tcenv);
                               debug = (uu___165_13581.debug);
                               delta_level = (uu___165_13581.delta_level);
                               primitive_steps =
                                 (uu___165_13581.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_13581.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_13581.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13584  ->
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
               let uu____13601 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13601 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13637 =
                               let uu___166_13638 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_13638.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_13638.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13637  in
                           let uu____13639 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13639 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13665 =
                                   FStar_List.map (fun uu____13681  -> dummy)
                                     lbs1
                                    in
                                 let uu____13682 =
                                   let uu____13691 =
                                     FStar_List.map
                                       (fun uu____13711  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13691 env  in
                                 FStar_List.append uu____13665 uu____13682
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13735 =
                                       let uu___167_13736 = rc  in
                                       let uu____13737 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_13736.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13737;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_13736.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13735
                                 | uu____13744 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_13748 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_13748.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_13748.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_13748.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_13748.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13758 =
                        FStar_List.map (fun uu____13774  -> dummy) lbs2  in
                      FStar_List.append uu____13758 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13782 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13782 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_13798 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_13798.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_13798.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13825 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13825
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13844 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13920  ->
                        match uu____13920 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_14041 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_14041.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_14041.FStar_Syntax_Syntax.sort)
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
               (match uu____13844 with
                | (rec_env,memos,uu____14254) ->
                    let uu____14307 =
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
                             let uu____14618 =
                               let uu____14625 =
                                 let uu____14626 =
                                   let uu____14657 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14657, false)
                                    in
                                 Clos uu____14626  in
                               (FStar_Pervasives_Native.None, uu____14625)
                                in
                             uu____14618 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14767  ->
                     let uu____14768 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14768);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14790 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14792::uu____14793 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14798) ->
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
                             | uu____14821 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14835 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14835
                              | uu____14846 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14850 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14876 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14894 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14911 =
                        let uu____14912 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14913 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14912 uu____14913
                         in
                      failwith uu____14911
                    else rebuild cfg env stack t2
                | uu____14915 -> norm cfg env stack t2))

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
                let uu____14925 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14925  in
              let uu____14926 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14926 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14939  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____14950  ->
                        let uu____14951 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14952 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14951 uu____14952);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____14957 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____14957 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14966))::stack1 ->
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
                      | uu____15021 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15024 ->
                          let uu____15027 =
                            let uu____15028 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15028
                             in
                          failwith uu____15027
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
                  let uu___171_15052 = cfg  in
                  let uu____15053 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____15053;
                    tcenv = (uu___171_15052.tcenv);
                    debug = (uu___171_15052.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_15052.primitive_steps);
                    strong = (uu___171_15052.strong);
                    memoize_lazy = (uu___171_15052.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_15052.normalize_pure_lets)
                  }
                else
                  (let uu___172_15055 = cfg  in
                   {
                     steps =
                       (let uu___173_15058 = cfg.steps  in
                        {
                          beta = (uu___173_15058.beta);
                          iota = (uu___173_15058.iota);
                          zeta = false;
                          weak = (uu___173_15058.weak);
                          hnf = (uu___173_15058.hnf);
                          primops = (uu___173_15058.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_15058.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_15058.unfold_until);
                          unfold_only = (uu___173_15058.unfold_only);
                          unfold_fully = (uu___173_15058.unfold_fully);
                          unfold_attr = (uu___173_15058.unfold_attr);
                          unfold_tac = (uu___173_15058.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_15058.pure_subterms_within_computations);
                          simplify = (uu___173_15058.simplify);
                          erase_universes = (uu___173_15058.erase_universes);
                          allow_unbound_universes =
                            (uu___173_15058.allow_unbound_universes);
                          reify_ = (uu___173_15058.reify_);
                          compress_uvars = (uu___173_15058.compress_uvars);
                          no_full_norm = (uu___173_15058.no_full_norm);
                          check_no_uvars = (uu___173_15058.check_no_uvars);
                          unmeta = (uu___173_15058.unmeta);
                          unascribe = (uu___173_15058.unascribe);
                          in_full_norm_request =
                            (uu___173_15058.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___173_15058.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___172_15055.tcenv);
                     debug = (uu___172_15055.debug);
                     delta_level = (uu___172_15055.delta_level);
                     primitive_steps = (uu___172_15055.primitive_steps);
                     strong = (uu___172_15055.strong);
                     memoize_lazy = (uu___172_15055.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_15055.normalize_pure_lets)
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
                  (fun uu____15088  ->
                     let uu____15089 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____15090 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15089
                       uu____15090);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____15092 =
                   let uu____15093 = FStar_Syntax_Subst.compress head3  in
                   uu____15093.FStar_Syntax_Syntax.n  in
                 match uu____15092 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____15111 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15111
                        in
                     let uu____15112 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15112 with
                      | (uu____15113,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15119 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15127 =
                                   let uu____15128 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____15128.FStar_Syntax_Syntax.n  in
                                 match uu____15127 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15134,uu____15135))
                                     ->
                                     let uu____15144 =
                                       let uu____15145 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____15145.FStar_Syntax_Syntax.n  in
                                     (match uu____15144 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15151,msrc,uu____15153))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15162 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15162
                                      | uu____15163 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15164 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____15165 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____15165 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_15170 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_15170.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_15170.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_15170.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_15170.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_15170.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____15171 = FStar_List.tl stack  in
                                    let uu____15172 =
                                      let uu____15173 =
                                        let uu____15176 =
                                          let uu____15177 =
                                            let uu____15190 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____15190)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15177
                                           in
                                        FStar_Syntax_Syntax.mk uu____15176
                                         in
                                      uu____15173
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____15171 uu____15172
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15206 =
                                      let uu____15207 = is_return body  in
                                      match uu____15207 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15211;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15212;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15217 -> false  in
                                    if uu____15206
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
                                         let uu____15240 =
                                           let uu____15243 =
                                             let uu____15244 =
                                               let uu____15261 =
                                                 let uu____15264 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____15264]  in
                                               (uu____15261, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15244
                                              in
                                           FStar_Syntax_Syntax.mk uu____15243
                                            in
                                         uu____15240
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____15280 =
                                           let uu____15281 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____15281.FStar_Syntax_Syntax.n
                                            in
                                         match uu____15280 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15287::uu____15288::[])
                                             ->
                                             let uu____15295 =
                                               let uu____15298 =
                                                 let uu____15299 =
                                                   let uu____15306 =
                                                     let uu____15309 =
                                                       let uu____15310 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15310
                                                        in
                                                     let uu____15311 =
                                                       let uu____15314 =
                                                         let uu____15315 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15315
                                                          in
                                                       [uu____15314]  in
                                                     uu____15309 ::
                                                       uu____15311
                                                      in
                                                   (bind1, uu____15306)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15299
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15298
                                                in
                                             uu____15295
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15323 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____15329 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____15329
                                         then
                                           let uu____15332 =
                                             let uu____15333 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____15333
                                              in
                                           let uu____15334 =
                                             let uu____15337 =
                                               let uu____15338 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____15338
                                                in
                                             [uu____15337]  in
                                           uu____15332 :: uu____15334
                                         else []  in
                                       let reified =
                                         let uu____15343 =
                                           let uu____15346 =
                                             let uu____15347 =
                                               let uu____15362 =
                                                 let uu____15365 =
                                                   let uu____15368 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____15369 =
                                                     let uu____15372 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____15372]  in
                                                   uu____15368 :: uu____15369
                                                    in
                                                 let uu____15373 =
                                                   let uu____15376 =
                                                     let uu____15379 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____15380 =
                                                       let uu____15383 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____15384 =
                                                         let uu____15387 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____15388 =
                                                           let uu____15391 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____15391]  in
                                                         uu____15387 ::
                                                           uu____15388
                                                          in
                                                       uu____15383 ::
                                                         uu____15384
                                                        in
                                                     uu____15379 ::
                                                       uu____15380
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____15376
                                                    in
                                                 FStar_List.append
                                                   uu____15365 uu____15373
                                                  in
                                               (bind_inst, uu____15362)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15347
                                              in
                                           FStar_Syntax_Syntax.mk uu____15346
                                            in
                                         uu____15343
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____15403  ->
                                            let uu____15404 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____15405 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15404 uu____15405);
                                       (let uu____15406 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____15406 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____15430 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15430
                        in
                     let uu____15431 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15431 with
                      | (uu____15432,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15467 =
                                  let uu____15468 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15468.FStar_Syntax_Syntax.n  in
                                match uu____15467 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15474) -> t2
                                | uu____15479 -> head4  in
                              let uu____15480 =
                                let uu____15481 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15481.FStar_Syntax_Syntax.n  in
                              match uu____15480 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15487 -> FStar_Pervasives_Native.None
                               in
                            let uu____15488 = maybe_extract_fv head4  in
                            match uu____15488 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15498 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15498
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____15503 = maybe_extract_fv head5
                                     in
                                  match uu____15503 with
                                  | FStar_Pervasives_Native.Some uu____15508
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15509 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____15514 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15529 =
                              match uu____15529 with
                              | (e,q) ->
                                  let uu____15536 =
                                    let uu____15537 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15537.FStar_Syntax_Syntax.n  in
                                  (match uu____15536 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____15552 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____15552
                                   | uu____15553 -> false)
                               in
                            let uu____15554 =
                              let uu____15555 =
                                let uu____15562 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15562 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15555
                               in
                            if uu____15554
                            then
                              let uu____15567 =
                                let uu____15568 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15568
                                 in
                              failwith uu____15567
                            else ());
                           (let uu____15570 = maybe_unfold_action head_app
                               in
                            match uu____15570 with
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
                                   (fun uu____15611  ->
                                      let uu____15612 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15613 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15612 uu____15613);
                                 (let uu____15614 = FStar_List.tl stack  in
                                  norm cfg env uu____15614 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15616) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15640 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15640  in
                     (log cfg
                        (fun uu____15644  ->
                           let uu____15645 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15645);
                      (let uu____15646 = FStar_List.tl stack  in
                       norm cfg env uu____15646 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15767  ->
                               match uu____15767 with
                               | (pat,wopt,tm) ->
                                   let uu____15815 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15815)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15847 = FStar_List.tl stack  in
                     norm cfg env uu____15847 tm
                 | uu____15848 -> fallback ())

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
              (fun uu____15862  ->
                 let uu____15863 = FStar_Ident.string_of_lid msrc  in
                 let uu____15864 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15865 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15863
                   uu____15864 uu____15865);
            (let uu____15866 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15866
             then
               let ed =
                 let uu____15868 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15868  in
               let uu____15869 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15869 with
               | (uu____15870,return_repr) ->
                   let return_inst =
                     let uu____15879 =
                       let uu____15880 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15880.FStar_Syntax_Syntax.n  in
                     match uu____15879 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15886::[]) ->
                         let uu____15893 =
                           let uu____15896 =
                             let uu____15897 =
                               let uu____15904 =
                                 let uu____15907 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15907]  in
                               (return_tm, uu____15904)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15897  in
                           FStar_Syntax_Syntax.mk uu____15896  in
                         uu____15893 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15915 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15918 =
                     let uu____15921 =
                       let uu____15922 =
                         let uu____15937 =
                           let uu____15940 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15941 =
                             let uu____15944 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15944]  in
                           uu____15940 :: uu____15941  in
                         (return_inst, uu____15937)  in
                       FStar_Syntax_Syntax.Tm_app uu____15922  in
                     FStar_Syntax_Syntax.mk uu____15921  in
                   uu____15918 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15953 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15953 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15956 =
                      let uu____15957 = FStar_Ident.text_of_lid msrc  in
                      let uu____15958 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15957 uu____15958
                       in
                    failwith uu____15956
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15959;
                      FStar_TypeChecker_Env.mtarget = uu____15960;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15961;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15976 =
                      let uu____15977 = FStar_Ident.text_of_lid msrc  in
                      let uu____15978 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15977 uu____15978
                       in
                    failwith uu____15976
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15979;
                      FStar_TypeChecker_Env.mtarget = uu____15980;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15981;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16005 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16006 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16005 t FStar_Syntax_Syntax.tun uu____16006))

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
                (fun uu____16062  ->
                   match uu____16062 with
                   | (a,imp) ->
                       let uu____16073 = norm cfg env [] a  in
                       (uu____16073, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____16081  ->
             let uu____16082 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16083 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____16082 uu____16083);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16107 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                     uu____16107
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_16110 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_16110.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_16110.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16130 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____16130
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_16133 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_16133.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_16133.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16166  ->
                      match uu____16166 with
                      | (a,i) ->
                          let uu____16177 = norm cfg env [] a  in
                          (uu____16177, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_16195  ->
                       match uu___90_16195 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16199 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16199
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_16207 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_16210 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_16210.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_16207.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_16207.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16213  ->
        match uu____16213 with
        | (x,imp) ->
            let uu____16216 =
              let uu___179_16217 = x  in
              let uu____16218 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_16217.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_16217.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16218
              }  in
            (uu____16216, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16224 =
          FStar_List.fold_left
            (fun uu____16242  ->
               fun b  ->
                 match uu____16242 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16224 with | (nbs,uu____16282) -> FStar_List.rev nbs

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
            let uu____16298 =
              let uu___180_16299 = rc  in
              let uu____16300 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_16299.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16300;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_16299.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16298
        | uu____16307 -> lopt

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
            (let uu____16328 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16329 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____16328
               uu____16329)
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
          let uu____16349 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____16349
          then tm1
          else
            (let w t =
               let uu___181_16361 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_16361.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_16361.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16370 =
                 let uu____16371 = FStar_Syntax_Util.unmeta t  in
                 uu____16371.FStar_Syntax_Syntax.n  in
               match uu____16370 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16378 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16423)::args1,(bv,uu____16426)::bs1) ->
                   let uu____16460 =
                     let uu____16461 = FStar_Syntax_Subst.compress t  in
                     uu____16461.FStar_Syntax_Syntax.n  in
                   (match uu____16460 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16465 -> false)
               | ([],[]) -> true
               | (uu____16486,uu____16487) -> false  in
             let is_applied bs t =
               let uu____16523 = FStar_Syntax_Util.head_and_args' t  in
               match uu____16523 with
               | (hd1,args) ->
                   let uu____16556 =
                     let uu____16557 = FStar_Syntax_Subst.compress hd1  in
                     uu____16557.FStar_Syntax_Syntax.n  in
                   (match uu____16556 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____16563 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____16575 = FStar_Syntax_Util.is_squash t  in
               match uu____16575 with
               | FStar_Pervasives_Native.Some (uu____16586,t') ->
                   is_applied bs t'
               | uu____16598 ->
                   let uu____16607 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____16607 with
                    | FStar_Pervasives_Native.Some (uu____16618,t') ->
                        is_applied bs t'
                    | uu____16630 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____16647 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16647 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16654)::(q,uu____16656)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____16691 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____16691 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____16696 =
                          let uu____16697 = FStar_Syntax_Subst.compress p  in
                          uu____16697.FStar_Syntax_Syntax.n  in
                        (match uu____16696 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16703 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____16703
                         | uu____16704 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____16707)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____16732 =
                          let uu____16733 = FStar_Syntax_Subst.compress p1
                             in
                          uu____16733.FStar_Syntax_Syntax.n  in
                        (match uu____16732 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16739 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____16739
                         | uu____16740 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____16744 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____16744 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____16749 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____16749 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16756 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16756
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____16759)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16784 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____16784 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16791 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16791
                              | uu____16792 -> FStar_Pervasives_Native.None)
                         | uu____16795 -> FStar_Pervasives_Native.None)
                    | uu____16798 -> FStar_Pervasives_Native.None)
               | uu____16801 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16812 =
                 let uu____16813 = FStar_Syntax_Subst.compress phi  in
                 uu____16813.FStar_Syntax_Syntax.n  in
               match uu____16812 with
               | FStar_Syntax_Syntax.Tm_match (uu____16818,br::brs) ->
                   let uu____16885 = br  in
                   (match uu____16885 with
                    | (uu____16902,uu____16903,e) ->
                        let r =
                          let uu____16924 = simp_t e  in
                          match uu____16924 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16930 =
                                FStar_List.for_all
                                  (fun uu____16948  ->
                                     match uu____16948 with
                                     | (uu____16961,uu____16962,e') ->
                                         let uu____16976 = simp_t e'  in
                                         uu____16976 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16930
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16984 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16989 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16989
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17010 =
                 match uu____17010 with
                 | (t1,q) ->
                     let uu____17023 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17023 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17051 -> (t1, q))
                  in
               let uu____17060 = FStar_Syntax_Util.head_and_args t  in
               match uu____17060 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____17122 =
                 let uu____17123 = FStar_Syntax_Util.unmeta ty  in
                 uu____17123.FStar_Syntax_Syntax.n  in
               match uu____17122 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17127) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17132,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17152 -> false  in
             let simplify1 arg =
               let uu____17175 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17175, arg)  in
             let uu____17184 = is_quantified_const tm1  in
             match uu____17184 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____17188 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____17188
             | FStar_Pervasives_Native.None  ->
                 let uu____17189 =
                   let uu____17190 = FStar_Syntax_Subst.compress tm1  in
                   uu____17190.FStar_Syntax_Syntax.n  in
                 (match uu____17189 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17194;
                              FStar_Syntax_Syntax.vars = uu____17195;_},uu____17196);
                         FStar_Syntax_Syntax.pos = uu____17197;
                         FStar_Syntax_Syntax.vars = uu____17198;_},args)
                      ->
                      let uu____17224 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17224
                      then
                        let uu____17225 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17225 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17272)::
                             (uu____17273,(arg,uu____17275))::[] ->
                             maybe_auto_squash arg
                         | (uu____17324,(arg,uu____17326))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17327)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17376)::uu____17377::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17428::(FStar_Pervasives_Native.Some (false
                                         ),uu____17429)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17480 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17494 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17494
                         then
                           let uu____17495 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17495 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17542)::uu____17543::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17594::(FStar_Pervasives_Native.Some (true
                                           ),uu____17595)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17646)::(uu____17647,(arg,uu____17649))::[]
                               -> maybe_auto_squash arg
                           | (uu____17698,(arg,uu____17700))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17701)::[]
                               -> maybe_auto_squash arg
                           | uu____17750 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17764 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17764
                            then
                              let uu____17765 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17765 with
                              | uu____17812::(FStar_Pervasives_Native.Some
                                              (true ),uu____17813)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17864)::uu____17865::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17916)::(uu____17917,(arg,uu____17919))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17968,(p,uu____17970))::(uu____17971,
                                                                (q,uu____17973))::[]
                                  ->
                                  let uu____18020 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18020
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18022 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18036 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18036
                               then
                                 let uu____18037 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18037 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18084)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18085)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18136)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18137)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18188)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18189)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18240)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18241)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18292,(arg,uu____18294))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18295)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18344)::(uu____18345,(arg,uu____18347))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18396,(arg,uu____18398))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18399)::[]
                                     ->
                                     let uu____18448 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18448
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18449)::(uu____18450,(arg,uu____18452))::[]
                                     ->
                                     let uu____18501 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18501
                                 | (uu____18502,(p,uu____18504))::(uu____18505,
                                                                   (q,uu____18507))::[]
                                     ->
                                     let uu____18554 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18554
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18556 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18570 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18570
                                  then
                                    let uu____18571 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18571 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18618)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18649)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18680 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18694 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18694
                                     then
                                       match args with
                                       | (t,uu____18696)::[] ->
                                           let uu____18713 =
                                             let uu____18714 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18714.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18713 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18717::[],body,uu____18719)
                                                ->
                                                let uu____18746 = simp_t body
                                                   in
                                                (match uu____18746 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18749 -> tm1)
                                            | uu____18752 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18754))::(t,uu____18756)::[]
                                           ->
                                           let uu____18795 =
                                             let uu____18796 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18796.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18795 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18799::[],body,uu____18801)
                                                ->
                                                let uu____18828 = simp_t body
                                                   in
                                                (match uu____18828 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18831 -> tm1)
                                            | uu____18834 -> tm1)
                                       | uu____18835 -> tm1
                                     else
                                       (let uu____18845 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18845
                                        then
                                          match args with
                                          | (t,uu____18847)::[] ->
                                              let uu____18864 =
                                                let uu____18865 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18865.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18864 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18868::[],body,uu____18870)
                                                   ->
                                                   let uu____18897 =
                                                     simp_t body  in
                                                   (match uu____18897 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18900 -> tm1)
                                               | uu____18903 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18905))::(t,uu____18907)::[]
                                              ->
                                              let uu____18946 =
                                                let uu____18947 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18947.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18946 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18950::[],body,uu____18952)
                                                   ->
                                                   let uu____18979 =
                                                     simp_t body  in
                                                   (match uu____18979 with
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
                                                    | uu____18982 -> tm1)
                                               | uu____18985 -> tm1)
                                          | uu____18986 -> tm1
                                        else
                                          (let uu____18996 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18996
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18997;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18998;_},uu____18999)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19016;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19017;_},uu____19018)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19035 -> tm1
                                           else
                                             (let uu____19045 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19045 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19065 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____19075;
                         FStar_Syntax_Syntax.vars = uu____19076;_},args)
                      ->
                      let uu____19098 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19098
                      then
                        let uu____19099 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19099 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19146)::
                             (uu____19147,(arg,uu____19149))::[] ->
                             maybe_auto_squash arg
                         | (uu____19198,(arg,uu____19200))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19201)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19250)::uu____19251::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19302::(FStar_Pervasives_Native.Some (false
                                         ),uu____19303)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19354 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19368 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19368
                         then
                           let uu____19369 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19369 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19416)::uu____19417::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19468::(FStar_Pervasives_Native.Some (true
                                           ),uu____19469)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19520)::(uu____19521,(arg,uu____19523))::[]
                               -> maybe_auto_squash arg
                           | (uu____19572,(arg,uu____19574))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19575)::[]
                               -> maybe_auto_squash arg
                           | uu____19624 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19638 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19638
                            then
                              let uu____19639 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19639 with
                              | uu____19686::(FStar_Pervasives_Native.Some
                                              (true ),uu____19687)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19738)::uu____19739::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19790)::(uu____19791,(arg,uu____19793))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19842,(p,uu____19844))::(uu____19845,
                                                                (q,uu____19847))::[]
                                  ->
                                  let uu____19894 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19894
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19896 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19910 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19910
                               then
                                 let uu____19911 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19911 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19958)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19959)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20010)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20011)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20062)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20063)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20114)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20115)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20166,(arg,uu____20168))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20169)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20218)::(uu____20219,(arg,uu____20221))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20270,(arg,uu____20272))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20273)::[]
                                     ->
                                     let uu____20322 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20322
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20323)::(uu____20324,(arg,uu____20326))::[]
                                     ->
                                     let uu____20375 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20375
                                 | (uu____20376,(p,uu____20378))::(uu____20379,
                                                                   (q,uu____20381))::[]
                                     ->
                                     let uu____20428 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20428
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20430 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20444 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20444
                                  then
                                    let uu____20445 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20445 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20492)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20523)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20554 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20568 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20568
                                     then
                                       match args with
                                       | (t,uu____20570)::[] ->
                                           let uu____20587 =
                                             let uu____20588 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20588.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20587 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20591::[],body,uu____20593)
                                                ->
                                                let uu____20620 = simp_t body
                                                   in
                                                (match uu____20620 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20623 -> tm1)
                                            | uu____20626 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20628))::(t,uu____20630)::[]
                                           ->
                                           let uu____20669 =
                                             let uu____20670 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20670.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20669 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20673::[],body,uu____20675)
                                                ->
                                                let uu____20702 = simp_t body
                                                   in
                                                (match uu____20702 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20705 -> tm1)
                                            | uu____20708 -> tm1)
                                       | uu____20709 -> tm1
                                     else
                                       (let uu____20719 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20719
                                        then
                                          match args with
                                          | (t,uu____20721)::[] ->
                                              let uu____20738 =
                                                let uu____20739 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20739.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20738 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20742::[],body,uu____20744)
                                                   ->
                                                   let uu____20771 =
                                                     simp_t body  in
                                                   (match uu____20771 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20774 -> tm1)
                                               | uu____20777 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20779))::(t,uu____20781)::[]
                                              ->
                                              let uu____20820 =
                                                let uu____20821 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20821.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20820 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20824::[],body,uu____20826)
                                                   ->
                                                   let uu____20853 =
                                                     simp_t body  in
                                                   (match uu____20853 with
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
                                                    | uu____20856 -> tm1)
                                               | uu____20859 -> tm1)
                                          | uu____20860 -> tm1
                                        else
                                          (let uu____20870 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20870
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20871;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20872;_},uu____20873)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20890;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20891;_},uu____20892)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20909 -> tm1
                                           else
                                             (let uu____20919 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20919 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20939 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20954 = simp_t t  in
                      (match uu____20954 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20957 ->
                      let uu____20980 = is_const_match tm1  in
                      (match uu____20980 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20983 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20993  ->
               (let uu____20995 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20996 = FStar_Syntax_Print.term_to_string t  in
                let uu____20997 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____21004 =
                  let uu____21005 =
                    let uu____21008 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____21008
                     in
                  stack_to_string uu____21005  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20995 uu____20996 uu____20997 uu____21004);
               (let uu____21031 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____21031
                then
                  let uu____21032 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____21032 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____21039 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____21040 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____21041 =
                          let uu____21042 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____21042
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____21039
                          uu____21040 uu____21041);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____21060 =
                     let uu____21061 =
                       let uu____21062 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____21062  in
                     FStar_Util.string_of_int uu____21061  in
                   let uu____21067 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____21068 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____21060 uu____21067 uu____21068)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____21074,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____21123  ->
                     let uu____21124 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____21124);
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
               let uu____21160 =
                 let uu___182_21161 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_21161.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_21161.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____21160
           | (Arg (Univ uu____21162,uu____21163,uu____21164))::uu____21165 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____21168,uu____21169))::uu____21170 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____21185,uu____21186),aq,r))::stack1
               when
               let uu____21236 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____21236 ->
               let t2 =
                 let uu____21240 =
                   let uu____21241 =
                     let uu____21242 = closure_as_term cfg env_arg tm  in
                     (uu____21242, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____21241  in
                 uu____21240 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____21248),aq,r))::stack1 ->
               (log cfg
                  (fun uu____21301  ->
                     let uu____21302 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____21302);
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
                  (let uu____21312 = FStar_ST.op_Bang m  in
                   match uu____21312 with
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
                   | FStar_Pervasives_Native.Some (uu____21449,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21496 =
                 log cfg
                   (fun uu____21500  ->
                      let uu____21501 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21501);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21505 =
                 let uu____21506 = FStar_Syntax_Subst.compress t1  in
                 uu____21506.FStar_Syntax_Syntax.n  in
               (match uu____21505 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21533 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21533  in
                    (log cfg
                       (fun uu____21537  ->
                          let uu____21538 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21538);
                     (let uu____21539 = FStar_List.tl stack  in
                      norm cfg env1 uu____21539 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21540);
                       FStar_Syntax_Syntax.pos = uu____21541;
                       FStar_Syntax_Syntax.vars = uu____21542;_},(e,uu____21544)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21573 when
                    (cfg.steps).primops ->
                    let uu____21588 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21588 with
                     | (hd1,args) ->
                         let uu____21625 =
                           let uu____21626 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21626.FStar_Syntax_Syntax.n  in
                         (match uu____21625 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21630 = find_prim_step cfg fv  in
                              (match uu____21630 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21633; arity = uu____21634;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21636;
                                     requires_binder_substitution =
                                       uu____21637;
                                     interpretation = uu____21638;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21651 -> fallback " (3)" ())
                          | uu____21654 -> fallback " (4)" ()))
                | uu____21655 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____21676  ->
                     let uu____21677 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21677);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21684 =
                   log cfg1
                     (fun uu____21689  ->
                        let uu____21690 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21691 =
                          let uu____21692 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21709  ->
                                    match uu____21709 with
                                    | (p,uu____21719,uu____21720) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21692
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21690 uu____21691);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_21737  ->
                                match uu___91_21737 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21738 -> false))
                         in
                      let steps =
                        let uu___183_21740 = cfg1.steps  in
                        {
                          beta = (uu___183_21740.beta);
                          iota = (uu___183_21740.iota);
                          zeta = false;
                          weak = (uu___183_21740.weak);
                          hnf = (uu___183_21740.hnf);
                          primops = (uu___183_21740.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_21740.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_21740.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_21740.pure_subterms_within_computations);
                          simplify = (uu___183_21740.simplify);
                          erase_universes = (uu___183_21740.erase_universes);
                          allow_unbound_universes =
                            (uu___183_21740.allow_unbound_universes);
                          reify_ = (uu___183_21740.reify_);
                          compress_uvars = (uu___183_21740.compress_uvars);
                          no_full_norm = (uu___183_21740.no_full_norm);
                          check_no_uvars = (uu___183_21740.check_no_uvars);
                          unmeta = (uu___183_21740.unmeta);
                          unascribe = (uu___183_21740.unascribe);
                          in_full_norm_request =
                            (uu___183_21740.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___183_21740.weakly_reduce_scrutinee)
                        }  in
                      let uu___184_21745 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_21745.tcenv);
                        debug = (uu___184_21745.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_21745.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_21745.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_21745.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21777 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21798 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21858  ->
                                    fun uu____21859  ->
                                      match (uu____21858, uu____21859) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21950 = norm_pat env3 p1
                                             in
                                          (match uu____21950 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21798 with
                           | (pats1,env3) ->
                               ((let uu___185_22032 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_22032.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_22051 = x  in
                            let uu____22052 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_22051.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_22051.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22052
                            }  in
                          ((let uu___187_22066 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_22066.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_22077 = x  in
                            let uu____22078 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_22077.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_22077.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22078
                            }  in
                          ((let uu___189_22092 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_22092.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_22108 = x  in
                            let uu____22109 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_22108.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_22108.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22109
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_22116 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_22116.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____22126 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____22140 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____22140 with
                                  | (p,wopt,e) ->
                                      let uu____22160 = norm_pat env1 p  in
                                      (match uu____22160 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22185 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22185
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22192 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____22192
                      then
                        norm
                          (let uu___192_22195 = cfg1  in
                           {
                             steps =
                               (let uu___193_22198 = cfg1.steps  in
                                {
                                  beta = (uu___193_22198.beta);
                                  iota = (uu___193_22198.iota);
                                  zeta = (uu___193_22198.zeta);
                                  weak = (uu___193_22198.weak);
                                  hnf = (uu___193_22198.hnf);
                                  primops = (uu___193_22198.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___193_22198.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___193_22198.unfold_until);
                                  unfold_only = (uu___193_22198.unfold_only);
                                  unfold_fully =
                                    (uu___193_22198.unfold_fully);
                                  unfold_attr = (uu___193_22198.unfold_attr);
                                  unfold_tac = (uu___193_22198.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___193_22198.pure_subterms_within_computations);
                                  simplify = (uu___193_22198.simplify);
                                  erase_universes =
                                    (uu___193_22198.erase_universes);
                                  allow_unbound_universes =
                                    (uu___193_22198.allow_unbound_universes);
                                  reify_ = (uu___193_22198.reify_);
                                  compress_uvars =
                                    (uu___193_22198.compress_uvars);
                                  no_full_norm =
                                    (uu___193_22198.no_full_norm);
                                  check_no_uvars =
                                    (uu___193_22198.check_no_uvars);
                                  unmeta = (uu___193_22198.unmeta);
                                  unascribe = (uu___193_22198.unascribe);
                                  in_full_norm_request =
                                    (uu___193_22198.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___192_22195.tcenv);
                             debug = (uu___192_22195.debug);
                             delta_level = (uu___192_22195.delta_level);
                             primitive_steps =
                               (uu___192_22195.primitive_steps);
                             strong = (uu___192_22195.strong);
                             memoize_lazy = (uu___192_22195.memoize_lazy);
                             normalize_pure_lets =
                               (uu___192_22195.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22200 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22200)
                    in
                 let rec is_cons head1 =
                   let uu____22205 =
                     let uu____22206 = FStar_Syntax_Subst.compress head1  in
                     uu____22206.FStar_Syntax_Syntax.n  in
                   match uu____22205 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22210) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22215 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22216;
                         FStar_Syntax_Syntax.fv_delta = uu____22217;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22218;
                         FStar_Syntax_Syntax.fv_delta = uu____22219;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22220);_}
                       -> true
                   | uu____22227 -> false  in
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
                   let uu____22372 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____22372 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22459 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22498 ->
                                 let uu____22499 =
                                   let uu____22500 = is_cons head1  in
                                   Prims.op_Negation uu____22500  in
                                 FStar_Util.Inr uu____22499)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22525 =
                              let uu____22526 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22526.FStar_Syntax_Syntax.n  in
                            (match uu____22525 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22544 ->
                                 let uu____22545 =
                                   let uu____22546 = is_cons head1  in
                                   Prims.op_Negation uu____22546  in
                                 FStar_Util.Inr uu____22545))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22615)::rest_a,(p1,uu____22618)::rest_p) ->
                       let uu____22662 = matches_pat t2 p1  in
                       (match uu____22662 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22711 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22817 = matches_pat scrutinee1 p1  in
                       (match uu____22817 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____22857  ->
                                  let uu____22858 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22859 =
                                    let uu____22860 =
                                      FStar_List.map
                                        (fun uu____22870  ->
                                           match uu____22870 with
                                           | (uu____22875,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22860
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22858 uu____22859);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22907  ->
                                       match uu____22907 with
                                       | (bv,t2) ->
                                           let uu____22930 =
                                             let uu____22937 =
                                               let uu____22940 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22940
                                                in
                                             let uu____22941 =
                                               let uu____22942 =
                                                 let uu____22973 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22973, false)
                                                  in
                                               Clos uu____22942  in
                                             (uu____22937, uu____22941)  in
                                           uu____22930 :: env2) env1 s
                                 in
                              let uu____23090 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23090)))
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
    let uu____23113 =
      let uu____23116 = FStar_ST.op_Bang plugins  in p :: uu____23116  in
    FStar_ST.op_Colon_Equals plugins uu____23113  in
  let retrieve uu____23214 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____23279  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_23312  ->
                  match uu___92_23312 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____23316 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____23322 -> d  in
        let uu____23325 = to_fsteps s  in
        let uu____23326 =
          let uu____23327 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____23328 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____23329 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____23330 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____23331 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____23327;
            primop = uu____23328;
            b380 = uu____23329;
            norm_delayed = uu____23330;
            print_normalized = uu____23331
          }  in
        let uu____23332 =
          let uu____23335 =
            let uu____23338 = retrieve_plugins ()  in
            FStar_List.append uu____23338 psteps  in
          add_steps built_in_primitive_steps uu____23335  in
        let uu____23341 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____23343 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____23343)
           in
        {
          steps = uu____23325;
          tcenv = e;
          debug = uu____23326;
          delta_level = d1;
          primitive_steps = uu____23332;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____23341
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
      fun t  -> let uu____23401 = config s e  in norm_comp uu____23401 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23414 = config [] env  in norm_universe uu____23414 [] u
  
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
        let uu____23432 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23432  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23439 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___194_23458 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___194_23458.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___194_23458.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23465 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23465
          then
            let ct1 =
              let uu____23467 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23467 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23474 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23474
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___195_23478 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___195_23478.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___195_23478.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___195_23478.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___196_23480 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___196_23480.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___196_23480.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___196_23480.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___196_23480.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___197_23481 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___197_23481.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_23481.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23483 -> c
  
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
        let uu____23495 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23495  in
      let uu____23502 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23502
      then
        let uu____23503 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23503 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23509  ->
                 let uu____23510 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23510)
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
            ((let uu____23527 =
                let uu____23532 =
                  let uu____23533 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23533
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23532)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23527);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23544 = config [AllowUnboundUniverses] env  in
          norm_comp uu____23544 [] c
        with
        | e ->
            ((let uu____23557 =
                let uu____23562 =
                  let uu____23563 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23563
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23562)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23557);
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
                   let uu____23600 =
                     let uu____23601 =
                       let uu____23608 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____23608)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23601  in
                   mk uu____23600 t01.FStar_Syntax_Syntax.pos
               | uu____23613 -> t2)
          | uu____23614 -> t2  in
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
        let uu____23654 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23654 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23683 ->
                 let uu____23690 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23690 with
                  | (actuals,uu____23700,uu____23701) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23715 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23715 with
                         | (binders,args) ->
                             let uu____23732 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23732
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
      | uu____23740 ->
          let uu____23741 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23741 with
           | (head1,args) ->
               let uu____23778 =
                 let uu____23779 = FStar_Syntax_Subst.compress head1  in
                 uu____23779.FStar_Syntax_Syntax.n  in
               (match uu____23778 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23782,thead) ->
                    let uu____23808 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23808 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23850 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___202_23858 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___202_23858.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___202_23858.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___202_23858.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___202_23858.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___202_23858.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___202_23858.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___202_23858.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___202_23858.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___202_23858.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___202_23858.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___202_23858.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___202_23858.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___202_23858.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___202_23858.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___202_23858.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___202_23858.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___202_23858.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___202_23858.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___202_23858.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___202_23858.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___202_23858.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___202_23858.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___202_23858.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___202_23858.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___202_23858.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___202_23858.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___202_23858.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___202_23858.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___202_23858.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___202_23858.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___202_23858.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___202_23858.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___202_23858.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___202_23858.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23850 with
                            | (uu____23859,ty,uu____23861) ->
                                eta_expand_with_type env t ty))
                | uu____23862 ->
                    let uu____23863 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___203_23871 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___203_23871.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___203_23871.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___203_23871.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___203_23871.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___203_23871.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___203_23871.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___203_23871.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___203_23871.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___203_23871.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___203_23871.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___203_23871.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___203_23871.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___203_23871.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___203_23871.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___203_23871.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___203_23871.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___203_23871.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___203_23871.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___203_23871.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___203_23871.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___203_23871.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___203_23871.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___203_23871.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___203_23871.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___203_23871.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___203_23871.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___203_23871.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___203_23871.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___203_23871.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___203_23871.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___203_23871.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___203_23871.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___203_23871.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___203_23871.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23863 with
                     | (uu____23872,ty,uu____23874) ->
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
      let uu___204_23931 = x  in
      let uu____23932 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___204_23931.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___204_23931.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23932
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23935 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23960 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23961 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23962 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23963 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23970 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23971 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23972 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___205_24000 = rc  in
          let uu____24001 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____24008 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___205_24000.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____24001;
            FStar_Syntax_Syntax.residual_flags = uu____24008
          }  in
        let uu____24011 =
          let uu____24012 =
            let uu____24029 = elim_delayed_subst_binders bs  in
            let uu____24036 = elim_delayed_subst_term t2  in
            let uu____24037 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____24029, uu____24036, uu____24037)  in
          FStar_Syntax_Syntax.Tm_abs uu____24012  in
        mk1 uu____24011
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____24066 =
          let uu____24067 =
            let uu____24080 = elim_delayed_subst_binders bs  in
            let uu____24087 = elim_delayed_subst_comp c  in
            (uu____24080, uu____24087)  in
          FStar_Syntax_Syntax.Tm_arrow uu____24067  in
        mk1 uu____24066
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24100 =
          let uu____24101 =
            let uu____24108 = elim_bv bv  in
            let uu____24109 = elim_delayed_subst_term phi  in
            (uu____24108, uu____24109)  in
          FStar_Syntax_Syntax.Tm_refine uu____24101  in
        mk1 uu____24100
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24132 =
          let uu____24133 =
            let uu____24148 = elim_delayed_subst_term t2  in
            let uu____24149 = elim_delayed_subst_args args  in
            (uu____24148, uu____24149)  in
          FStar_Syntax_Syntax.Tm_app uu____24133  in
        mk1 uu____24132
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___206_24213 = p  in
              let uu____24214 =
                let uu____24215 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24215  in
              {
                FStar_Syntax_Syntax.v = uu____24214;
                FStar_Syntax_Syntax.p =
                  (uu___206_24213.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___207_24217 = p  in
              let uu____24218 =
                let uu____24219 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24219  in
              {
                FStar_Syntax_Syntax.v = uu____24218;
                FStar_Syntax_Syntax.p =
                  (uu___207_24217.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___208_24226 = p  in
              let uu____24227 =
                let uu____24228 =
                  let uu____24235 = elim_bv x  in
                  let uu____24236 = elim_delayed_subst_term t0  in
                  (uu____24235, uu____24236)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24228  in
              {
                FStar_Syntax_Syntax.v = uu____24227;
                FStar_Syntax_Syntax.p =
                  (uu___208_24226.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___209_24255 = p  in
              let uu____24256 =
                let uu____24257 =
                  let uu____24270 =
                    FStar_List.map
                      (fun uu____24293  ->
                         match uu____24293 with
                         | (x,b) ->
                             let uu____24306 = elim_pat x  in
                             (uu____24306, b)) pats
                     in
                  (fv, uu____24270)  in
                FStar_Syntax_Syntax.Pat_cons uu____24257  in
              {
                FStar_Syntax_Syntax.v = uu____24256;
                FStar_Syntax_Syntax.p =
                  (uu___209_24255.FStar_Syntax_Syntax.p)
              }
          | uu____24319 -> p  in
        let elim_branch uu____24341 =
          match uu____24341 with
          | (pat,wopt,t3) ->
              let uu____24367 = elim_pat pat  in
              let uu____24370 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24373 = elim_delayed_subst_term t3  in
              (uu____24367, uu____24370, uu____24373)
           in
        let uu____24378 =
          let uu____24379 =
            let uu____24402 = elim_delayed_subst_term t2  in
            let uu____24403 = FStar_List.map elim_branch branches  in
            (uu____24402, uu____24403)  in
          FStar_Syntax_Syntax.Tm_match uu____24379  in
        mk1 uu____24378
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24512 =
          match uu____24512 with
          | (tc,topt) ->
              let uu____24547 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24557 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24557
                | FStar_Util.Inr c ->
                    let uu____24559 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24559
                 in
              let uu____24560 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24547, uu____24560)
           in
        let uu____24569 =
          let uu____24570 =
            let uu____24597 = elim_delayed_subst_term t2  in
            let uu____24598 = elim_ascription a  in
            (uu____24597, uu____24598, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24570  in
        mk1 uu____24569
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___210_24643 = lb  in
          let uu____24644 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24647 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___210_24643.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___210_24643.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24644;
            FStar_Syntax_Syntax.lbeff =
              (uu___210_24643.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24647;
            FStar_Syntax_Syntax.lbattrs =
              (uu___210_24643.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___210_24643.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24650 =
          let uu____24651 =
            let uu____24664 =
              let uu____24671 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24671)  in
            let uu____24680 = elim_delayed_subst_term t2  in
            (uu____24664, uu____24680)  in
          FStar_Syntax_Syntax.Tm_let uu____24651  in
        mk1 uu____24650
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24713 =
          let uu____24714 =
            let uu____24731 = elim_delayed_subst_term t2  in
            (uv, uu____24731)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24714  in
        mk1 uu____24713
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24749 =
          let uu____24750 =
            let uu____24757 = elim_delayed_subst_term tm  in
            (uu____24757, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24750  in
        mk1 uu____24749
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24764 =
          let uu____24765 =
            let uu____24772 = elim_delayed_subst_term t2  in
            let uu____24773 = elim_delayed_subst_meta md  in
            (uu____24772, uu____24773)  in
          FStar_Syntax_Syntax.Tm_meta uu____24765  in
        mk1 uu____24764

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24780  ->
         match uu___93_24780 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24784 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24784
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
        let uu____24805 =
          let uu____24806 =
            let uu____24815 = elim_delayed_subst_term t  in
            (uu____24815, uopt)  in
          FStar_Syntax_Syntax.Total uu____24806  in
        mk1 uu____24805
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24828 =
          let uu____24829 =
            let uu____24838 = elim_delayed_subst_term t  in
            (uu____24838, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24829  in
        mk1 uu____24828
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___211_24843 = ct  in
          let uu____24844 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24847 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24856 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___211_24843.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___211_24843.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24844;
            FStar_Syntax_Syntax.effect_args = uu____24847;
            FStar_Syntax_Syntax.flags = uu____24856
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24859  ->
    match uu___94_24859 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24871 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24871
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24904 =
          let uu____24911 = elim_delayed_subst_term t  in (m, uu____24911)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24904
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24919 =
          let uu____24928 = elim_delayed_subst_term t  in
          (m1, m2, uu____24928)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24919
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24951  ->
         match uu____24951 with
         | (t,q) ->
             let uu____24962 = elim_delayed_subst_term t  in (uu____24962, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24982  ->
         match uu____24982 with
         | (x,q) ->
             let uu____24993 =
               let uu___212_24994 = x  in
               let uu____24995 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___212_24994.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___212_24994.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24995
               }  in
             (uu____24993, q)) bs

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
            | (uu____25071,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25077,FStar_Util.Inl t) ->
                let uu____25083 =
                  let uu____25086 =
                    let uu____25087 =
                      let uu____25100 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25100)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25087  in
                  FStar_Syntax_Syntax.mk uu____25086  in
                uu____25083 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25104 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25104 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25132 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25187 ->
                    let uu____25188 =
                      let uu____25197 =
                        let uu____25198 = FStar_Syntax_Subst.compress t4  in
                        uu____25198.FStar_Syntax_Syntax.n  in
                      (uu____25197, tc)  in
                    (match uu____25188 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25223) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25260) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25299,FStar_Util.Inl uu____25300) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25323 -> failwith "Impossible")
                 in
              (match uu____25132 with
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
          let uu____25428 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25428 with
          | (univ_names1,binders1,tc) ->
              let uu____25486 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25486)
  
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
          let uu____25521 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25521 with
          | (univ_names1,binders1,tc) ->
              let uu____25581 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25581)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25614 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25614 with
           | (univ_names1,binders1,typ1) ->
               let uu___213_25642 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_25642.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_25642.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_25642.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_25642.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___214_25663 = s  in
          let uu____25664 =
            let uu____25665 =
              let uu____25674 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25674, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25665  in
          {
            FStar_Syntax_Syntax.sigel = uu____25664;
            FStar_Syntax_Syntax.sigrng =
              (uu___214_25663.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_25663.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_25663.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_25663.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25691 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25691 with
           | (univ_names1,uu____25709,typ1) ->
               let uu___215_25723 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_25723.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_25723.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_25723.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_25723.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25729 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25729 with
           | (univ_names1,uu____25747,typ1) ->
               let uu___216_25761 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_25761.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_25761.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_25761.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___216_25761.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25795 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25795 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25818 =
                            let uu____25819 =
                              let uu____25820 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25820  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25819
                             in
                          elim_delayed_subst_term uu____25818  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___217_25823 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___217_25823.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___217_25823.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___217_25823.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___217_25823.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___218_25824 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___218_25824.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___218_25824.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___218_25824.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___218_25824.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___219_25836 = s  in
          let uu____25837 =
            let uu____25838 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25838  in
          {
            FStar_Syntax_Syntax.sigel = uu____25837;
            FStar_Syntax_Syntax.sigrng =
              (uu___219_25836.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___219_25836.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___219_25836.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___219_25836.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25842 = elim_uvars_aux_t env us [] t  in
          (match uu____25842 with
           | (us1,uu____25860,t1) ->
               let uu___220_25874 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___220_25874.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___220_25874.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___220_25874.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___220_25874.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25875 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25877 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25877 with
           | (univs1,binders,signature) ->
               let uu____25905 =
                 let uu____25914 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____25914 with
                 | (univs_opening,univs2) ->
                     let uu____25941 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25941)
                  in
               (match uu____25905 with
                | (univs_opening,univs_closing) ->
                    let uu____25958 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25964 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25965 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25964, uu____25965)  in
                    (match uu____25958 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____25987 =
                           match uu____25987 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26005 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26005 with
                                | (us1,t1) ->
                                    let uu____26016 =
                                      let uu____26021 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26028 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26021, uu____26028)  in
                                    (match uu____26016 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26041 =
                                           let uu____26046 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26055 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26046, uu____26055)  in
                                         (match uu____26041 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26071 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26071
                                                 in
                                              let uu____26072 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26072 with
                                               | (uu____26093,uu____26094,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26109 =
                                                       let uu____26110 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26110
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26109
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26115 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26115 with
                           | (uu____26128,uu____26129,t1) -> t1  in
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
                             | uu____26189 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26206 =
                               let uu____26207 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26207.FStar_Syntax_Syntax.n  in
                             match uu____26206 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26266 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26295 =
                               let uu____26296 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26296.FStar_Syntax_Syntax.n  in
                             match uu____26295 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26317) ->
                                 let uu____26338 = destruct_action_body body
                                    in
                                 (match uu____26338 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26383 ->
                                 let uu____26384 = destruct_action_body t  in
                                 (match uu____26384 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26433 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26433 with
                           | (action_univs,t) ->
                               let uu____26442 = destruct_action_typ_templ t
                                  in
                               (match uu____26442 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___221_26483 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___221_26483.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___221_26483.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___222_26485 = ed  in
                           let uu____26486 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26487 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26488 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26489 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26490 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26491 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26492 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26493 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26494 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26495 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26496 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26497 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26498 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26499 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___222_26485.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___222_26485.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26486;
                             FStar_Syntax_Syntax.bind_wp = uu____26487;
                             FStar_Syntax_Syntax.if_then_else = uu____26488;
                             FStar_Syntax_Syntax.ite_wp = uu____26489;
                             FStar_Syntax_Syntax.stronger = uu____26490;
                             FStar_Syntax_Syntax.close_wp = uu____26491;
                             FStar_Syntax_Syntax.assert_p = uu____26492;
                             FStar_Syntax_Syntax.assume_p = uu____26493;
                             FStar_Syntax_Syntax.null_wp = uu____26494;
                             FStar_Syntax_Syntax.trivial = uu____26495;
                             FStar_Syntax_Syntax.repr = uu____26496;
                             FStar_Syntax_Syntax.return_repr = uu____26497;
                             FStar_Syntax_Syntax.bind_repr = uu____26498;
                             FStar_Syntax_Syntax.actions = uu____26499;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___222_26485.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___223_26502 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___223_26502.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___223_26502.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___223_26502.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___223_26502.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_26519 =
            match uu___95_26519 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26546 = elim_uvars_aux_t env us [] t  in
                (match uu____26546 with
                 | (us1,uu____26570,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___224_26589 = sub_eff  in
            let uu____26590 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26593 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___224_26589.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___224_26589.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26590;
              FStar_Syntax_Syntax.lift = uu____26593
            }  in
          let uu___225_26596 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___225_26596.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___225_26596.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___225_26596.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___225_26596.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26606 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26606 with
           | (univ_names1,binders1,comp1) ->
               let uu___226_26640 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___226_26640.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___226_26640.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___226_26640.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___226_26640.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26651 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26652 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  