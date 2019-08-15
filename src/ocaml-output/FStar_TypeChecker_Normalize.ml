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
  fun projectee  -> match projectee with | Beta  -> true | uu____35 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____41 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____47 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____54 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____67 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____73 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____79 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____85 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____91 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____97 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____104 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____120 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____142 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____162 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____175 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____181 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____187 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____193 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____199 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____205 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____211 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____217 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____223 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____229 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____235 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____248 'Auu____249 .
    ('Auu____248 -> 'Auu____249) ->
      'Auu____249 ->
        'Auu____248 FStar_Pervasives_Native.option -> 'Auu____249
  =
  fun f  ->
    fun d  ->
      fun uu___77_269  ->
        match uu___77_269 with
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
      let add_opt x uu___78_1503 =
        match uu___78_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1523 = fs  in
          {
            beta = true;
            iota = (uu___96_1523.iota);
            zeta = (uu___96_1523.zeta);
            weak = (uu___96_1523.weak);
            hnf = (uu___96_1523.hnf);
            primops = (uu___96_1523.primops);
            do_not_unfold_pure_lets = (uu___96_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1523.unfold_until);
            unfold_only = (uu___96_1523.unfold_only);
            unfold_fully = (uu___96_1523.unfold_fully);
            unfold_attr = (uu___96_1523.unfold_attr);
            unfold_tac = (uu___96_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1523.pure_subterms_within_computations);
            simplify = (uu___96_1523.simplify);
            erase_universes = (uu___96_1523.erase_universes);
            allow_unbound_universes = (uu___96_1523.allow_unbound_universes);
            reify_ = (uu___96_1523.reify_);
            compress_uvars = (uu___96_1523.compress_uvars);
            no_full_norm = (uu___96_1523.no_full_norm);
            check_no_uvars = (uu___96_1523.check_no_uvars);
            unmeta = (uu___96_1523.unmeta);
            unascribe = (uu___96_1523.unascribe);
            in_full_norm_request = (uu___96_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___96_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___97_1524 = fs  in
          {
            beta = (uu___97_1524.beta);
            iota = true;
            zeta = (uu___97_1524.zeta);
            weak = (uu___97_1524.weak);
            hnf = (uu___97_1524.hnf);
            primops = (uu___97_1524.primops);
            do_not_unfold_pure_lets = (uu___97_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1524.unfold_until);
            unfold_only = (uu___97_1524.unfold_only);
            unfold_fully = (uu___97_1524.unfold_fully);
            unfold_attr = (uu___97_1524.unfold_attr);
            unfold_tac = (uu___97_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1524.pure_subterms_within_computations);
            simplify = (uu___97_1524.simplify);
            erase_universes = (uu___97_1524.erase_universes);
            allow_unbound_universes = (uu___97_1524.allow_unbound_universes);
            reify_ = (uu___97_1524.reify_);
            compress_uvars = (uu___97_1524.compress_uvars);
            no_full_norm = (uu___97_1524.no_full_norm);
            check_no_uvars = (uu___97_1524.check_no_uvars);
            unmeta = (uu___97_1524.unmeta);
            unascribe = (uu___97_1524.unascribe);
            in_full_norm_request = (uu___97_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___98_1525 = fs  in
          {
            beta = (uu___98_1525.beta);
            iota = (uu___98_1525.iota);
            zeta = true;
            weak = (uu___98_1525.weak);
            hnf = (uu___98_1525.hnf);
            primops = (uu___98_1525.primops);
            do_not_unfold_pure_lets = (uu___98_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1525.unfold_until);
            unfold_only = (uu___98_1525.unfold_only);
            unfold_fully = (uu___98_1525.unfold_fully);
            unfold_attr = (uu___98_1525.unfold_attr);
            unfold_tac = (uu___98_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1525.pure_subterms_within_computations);
            simplify = (uu___98_1525.simplify);
            erase_universes = (uu___98_1525.erase_universes);
            allow_unbound_universes = (uu___98_1525.allow_unbound_universes);
            reify_ = (uu___98_1525.reify_);
            compress_uvars = (uu___98_1525.compress_uvars);
            no_full_norm = (uu___98_1525.no_full_norm);
            check_no_uvars = (uu___98_1525.check_no_uvars);
            unmeta = (uu___98_1525.unmeta);
            unascribe = (uu___98_1525.unascribe);
            in_full_norm_request = (uu___98_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___98_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___99_1526 = fs  in
          {
            beta = false;
            iota = (uu___99_1526.iota);
            zeta = (uu___99_1526.zeta);
            weak = (uu___99_1526.weak);
            hnf = (uu___99_1526.hnf);
            primops = (uu___99_1526.primops);
            do_not_unfold_pure_lets = (uu___99_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1526.unfold_until);
            unfold_only = (uu___99_1526.unfold_only);
            unfold_fully = (uu___99_1526.unfold_fully);
            unfold_attr = (uu___99_1526.unfold_attr);
            unfold_tac = (uu___99_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1526.pure_subterms_within_computations);
            simplify = (uu___99_1526.simplify);
            erase_universes = (uu___99_1526.erase_universes);
            allow_unbound_universes = (uu___99_1526.allow_unbound_universes);
            reify_ = (uu___99_1526.reify_);
            compress_uvars = (uu___99_1526.compress_uvars);
            no_full_norm = (uu___99_1526.no_full_norm);
            check_no_uvars = (uu___99_1526.check_no_uvars);
            unmeta = (uu___99_1526.unmeta);
            unascribe = (uu___99_1526.unascribe);
            in_full_norm_request = (uu___99_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___99_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___100_1527 = fs  in
          {
            beta = (uu___100_1527.beta);
            iota = false;
            zeta = (uu___100_1527.zeta);
            weak = (uu___100_1527.weak);
            hnf = (uu___100_1527.hnf);
            primops = (uu___100_1527.primops);
            do_not_unfold_pure_lets = (uu___100_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1527.unfold_until);
            unfold_only = (uu___100_1527.unfold_only);
            unfold_fully = (uu___100_1527.unfold_fully);
            unfold_attr = (uu___100_1527.unfold_attr);
            unfold_tac = (uu___100_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1527.pure_subterms_within_computations);
            simplify = (uu___100_1527.simplify);
            erase_universes = (uu___100_1527.erase_universes);
            allow_unbound_universes = (uu___100_1527.allow_unbound_universes);
            reify_ = (uu___100_1527.reify_);
            compress_uvars = (uu___100_1527.compress_uvars);
            no_full_norm = (uu___100_1527.no_full_norm);
            check_no_uvars = (uu___100_1527.check_no_uvars);
            unmeta = (uu___100_1527.unmeta);
            unascribe = (uu___100_1527.unascribe);
            in_full_norm_request = (uu___100_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___101_1528 = fs  in
          {
            beta = (uu___101_1528.beta);
            iota = (uu___101_1528.iota);
            zeta = false;
            weak = (uu___101_1528.weak);
            hnf = (uu___101_1528.hnf);
            primops = (uu___101_1528.primops);
            do_not_unfold_pure_lets = (uu___101_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1528.unfold_until);
            unfold_only = (uu___101_1528.unfold_only);
            unfold_fully = (uu___101_1528.unfold_fully);
            unfold_attr = (uu___101_1528.unfold_attr);
            unfold_tac = (uu___101_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1528.pure_subterms_within_computations);
            simplify = (uu___101_1528.simplify);
            erase_universes = (uu___101_1528.erase_universes);
            allow_unbound_universes = (uu___101_1528.allow_unbound_universes);
            reify_ = (uu___101_1528.reify_);
            compress_uvars = (uu___101_1528.compress_uvars);
            no_full_norm = (uu___101_1528.no_full_norm);
            check_no_uvars = (uu___101_1528.check_no_uvars);
            unmeta = (uu___101_1528.unmeta);
            unascribe = (uu___101_1528.unascribe);
            in_full_norm_request = (uu___101_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___101_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1530 = fs  in
          {
            beta = (uu___102_1530.beta);
            iota = (uu___102_1530.iota);
            zeta = (uu___102_1530.zeta);
            weak = true;
            hnf = (uu___102_1530.hnf);
            primops = (uu___102_1530.primops);
            do_not_unfold_pure_lets = (uu___102_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1530.unfold_until);
            unfold_only = (uu___102_1530.unfold_only);
            unfold_fully = (uu___102_1530.unfold_fully);
            unfold_attr = (uu___102_1530.unfold_attr);
            unfold_tac = (uu___102_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1530.pure_subterms_within_computations);
            simplify = (uu___102_1530.simplify);
            erase_universes = (uu___102_1530.erase_universes);
            allow_unbound_universes = (uu___102_1530.allow_unbound_universes);
            reify_ = (uu___102_1530.reify_);
            compress_uvars = (uu___102_1530.compress_uvars);
            no_full_norm = (uu___102_1530.no_full_norm);
            check_no_uvars = (uu___102_1530.check_no_uvars);
            unmeta = (uu___102_1530.unmeta);
            unascribe = (uu___102_1530.unascribe);
            in_full_norm_request = (uu___102_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___102_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___103_1531 = fs  in
          {
            beta = (uu___103_1531.beta);
            iota = (uu___103_1531.iota);
            zeta = (uu___103_1531.zeta);
            weak = (uu___103_1531.weak);
            hnf = true;
            primops = (uu___103_1531.primops);
            do_not_unfold_pure_lets = (uu___103_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1531.unfold_until);
            unfold_only = (uu___103_1531.unfold_only);
            unfold_fully = (uu___103_1531.unfold_fully);
            unfold_attr = (uu___103_1531.unfold_attr);
            unfold_tac = (uu___103_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1531.pure_subterms_within_computations);
            simplify = (uu___103_1531.simplify);
            erase_universes = (uu___103_1531.erase_universes);
            allow_unbound_universes = (uu___103_1531.allow_unbound_universes);
            reify_ = (uu___103_1531.reify_);
            compress_uvars = (uu___103_1531.compress_uvars);
            no_full_norm = (uu___103_1531.no_full_norm);
            check_no_uvars = (uu___103_1531.check_no_uvars);
            unmeta = (uu___103_1531.unmeta);
            unascribe = (uu___103_1531.unascribe);
            in_full_norm_request = (uu___103_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___104_1532 = fs  in
          {
            beta = (uu___104_1532.beta);
            iota = (uu___104_1532.iota);
            zeta = (uu___104_1532.zeta);
            weak = (uu___104_1532.weak);
            hnf = (uu___104_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1532.unfold_until);
            unfold_only = (uu___104_1532.unfold_only);
            unfold_fully = (uu___104_1532.unfold_fully);
            unfold_attr = (uu___104_1532.unfold_attr);
            unfold_tac = (uu___104_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1532.pure_subterms_within_computations);
            simplify = (uu___104_1532.simplify);
            erase_universes = (uu___104_1532.erase_universes);
            allow_unbound_universes = (uu___104_1532.allow_unbound_universes);
            reify_ = (uu___104_1532.reify_);
            compress_uvars = (uu___104_1532.compress_uvars);
            no_full_norm = (uu___104_1532.no_full_norm);
            check_no_uvars = (uu___104_1532.check_no_uvars);
            unmeta = (uu___104_1532.unmeta);
            unascribe = (uu___104_1532.unascribe);
            in_full_norm_request = (uu___104_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1533 = fs  in
          {
            beta = (uu___105_1533.beta);
            iota = (uu___105_1533.iota);
            zeta = (uu___105_1533.zeta);
            weak = (uu___105_1533.weak);
            hnf = (uu___105_1533.hnf);
            primops = (uu___105_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1533.unfold_until);
            unfold_only = (uu___105_1533.unfold_only);
            unfold_fully = (uu___105_1533.unfold_fully);
            unfold_attr = (uu___105_1533.unfold_attr);
            unfold_tac = (uu___105_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1533.pure_subterms_within_computations);
            simplify = (uu___105_1533.simplify);
            erase_universes = (uu___105_1533.erase_universes);
            allow_unbound_universes = (uu___105_1533.allow_unbound_universes);
            reify_ = (uu___105_1533.reify_);
            compress_uvars = (uu___105_1533.compress_uvars);
            no_full_norm = (uu___105_1533.no_full_norm);
            check_no_uvars = (uu___105_1533.check_no_uvars);
            unmeta = (uu___105_1533.unmeta);
            unascribe = (uu___105_1533.unascribe);
            in_full_norm_request = (uu___105_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___105_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___106_1535 = fs  in
          {
            beta = (uu___106_1535.beta);
            iota = (uu___106_1535.iota);
            zeta = (uu___106_1535.zeta);
            weak = (uu___106_1535.weak);
            hnf = (uu___106_1535.hnf);
            primops = (uu___106_1535.primops);
            do_not_unfold_pure_lets = (uu___106_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1535.unfold_only);
            unfold_fully = (uu___106_1535.unfold_fully);
            unfold_attr = (uu___106_1535.unfold_attr);
            unfold_tac = (uu___106_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1535.pure_subterms_within_computations);
            simplify = (uu___106_1535.simplify);
            erase_universes = (uu___106_1535.erase_universes);
            allow_unbound_universes = (uu___106_1535.allow_unbound_universes);
            reify_ = (uu___106_1535.reify_);
            compress_uvars = (uu___106_1535.compress_uvars);
            no_full_norm = (uu___106_1535.no_full_norm);
            check_no_uvars = (uu___106_1535.check_no_uvars);
            unmeta = (uu___106_1535.unmeta);
            unascribe = (uu___106_1535.unascribe);
            in_full_norm_request = (uu___106_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___107_1539 = fs  in
          {
            beta = (uu___107_1539.beta);
            iota = (uu___107_1539.iota);
            zeta = (uu___107_1539.zeta);
            weak = (uu___107_1539.weak);
            hnf = (uu___107_1539.hnf);
            primops = (uu___107_1539.primops);
            do_not_unfold_pure_lets = (uu___107_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1539.unfold_fully);
            unfold_attr = (uu___107_1539.unfold_attr);
            unfold_tac = (uu___107_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1539.pure_subterms_within_computations);
            simplify = (uu___107_1539.simplify);
            erase_universes = (uu___107_1539.erase_universes);
            allow_unbound_universes = (uu___107_1539.allow_unbound_universes);
            reify_ = (uu___107_1539.reify_);
            compress_uvars = (uu___107_1539.compress_uvars);
            no_full_norm = (uu___107_1539.no_full_norm);
            check_no_uvars = (uu___107_1539.check_no_uvars);
            unmeta = (uu___107_1539.unmeta);
            unascribe = (uu___107_1539.unascribe);
            in_full_norm_request = (uu___107_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___107_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___108_1545 = fs  in
          {
            beta = (uu___108_1545.beta);
            iota = (uu___108_1545.iota);
            zeta = (uu___108_1545.zeta);
            weak = (uu___108_1545.weak);
            hnf = (uu___108_1545.hnf);
            primops = (uu___108_1545.primops);
            do_not_unfold_pure_lets = (uu___108_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1545.unfold_until);
            unfold_only = (uu___108_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1545.unfold_attr);
            unfold_tac = (uu___108_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1545.pure_subterms_within_computations);
            simplify = (uu___108_1545.simplify);
            erase_universes = (uu___108_1545.erase_universes);
            allow_unbound_universes = (uu___108_1545.allow_unbound_universes);
            reify_ = (uu___108_1545.reify_);
            compress_uvars = (uu___108_1545.compress_uvars);
            no_full_norm = (uu___108_1545.no_full_norm);
            check_no_uvars = (uu___108_1545.check_no_uvars);
            unmeta = (uu___108_1545.unmeta);
            unascribe = (uu___108_1545.unascribe);
            in_full_norm_request = (uu___108_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___109_1549 = fs  in
          {
            beta = (uu___109_1549.beta);
            iota = (uu___109_1549.iota);
            zeta = (uu___109_1549.zeta);
            weak = (uu___109_1549.weak);
            hnf = (uu___109_1549.hnf);
            primops = (uu___109_1549.primops);
            do_not_unfold_pure_lets = (uu___109_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1549.unfold_until);
            unfold_only = (uu___109_1549.unfold_only);
            unfold_fully = (uu___109_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1549.pure_subterms_within_computations);
            simplify = (uu___109_1549.simplify);
            erase_universes = (uu___109_1549.erase_universes);
            allow_unbound_universes = (uu___109_1549.allow_unbound_universes);
            reify_ = (uu___109_1549.reify_);
            compress_uvars = (uu___109_1549.compress_uvars);
            no_full_norm = (uu___109_1549.no_full_norm);
            check_no_uvars = (uu___109_1549.check_no_uvars);
            unmeta = (uu___109_1549.unmeta);
            unascribe = (uu___109_1549.unascribe);
            in_full_norm_request = (uu___109_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___109_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___110_1550 = fs  in
          {
            beta = (uu___110_1550.beta);
            iota = (uu___110_1550.iota);
            zeta = (uu___110_1550.zeta);
            weak = (uu___110_1550.weak);
            hnf = (uu___110_1550.hnf);
            primops = (uu___110_1550.primops);
            do_not_unfold_pure_lets = (uu___110_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1550.unfold_until);
            unfold_only = (uu___110_1550.unfold_only);
            unfold_fully = (uu___110_1550.unfold_fully);
            unfold_attr = (uu___110_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1550.pure_subterms_within_computations);
            simplify = (uu___110_1550.simplify);
            erase_universes = (uu___110_1550.erase_universes);
            allow_unbound_universes = (uu___110_1550.allow_unbound_universes);
            reify_ = (uu___110_1550.reify_);
            compress_uvars = (uu___110_1550.compress_uvars);
            no_full_norm = (uu___110_1550.no_full_norm);
            check_no_uvars = (uu___110_1550.check_no_uvars);
            unmeta = (uu___110_1550.unmeta);
            unascribe = (uu___110_1550.unascribe);
            in_full_norm_request = (uu___110_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1551 = fs  in
          {
            beta = (uu___111_1551.beta);
            iota = (uu___111_1551.iota);
            zeta = (uu___111_1551.zeta);
            weak = (uu___111_1551.weak);
            hnf = (uu___111_1551.hnf);
            primops = (uu___111_1551.primops);
            do_not_unfold_pure_lets = (uu___111_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1551.unfold_until);
            unfold_only = (uu___111_1551.unfold_only);
            unfold_fully = (uu___111_1551.unfold_fully);
            unfold_attr = (uu___111_1551.unfold_attr);
            unfold_tac = (uu___111_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1551.simplify);
            erase_universes = (uu___111_1551.erase_universes);
            allow_unbound_universes = (uu___111_1551.allow_unbound_universes);
            reify_ = (uu___111_1551.reify_);
            compress_uvars = (uu___111_1551.compress_uvars);
            no_full_norm = (uu___111_1551.no_full_norm);
            check_no_uvars = (uu___111_1551.check_no_uvars);
            unmeta = (uu___111_1551.unmeta);
            unascribe = (uu___111_1551.unascribe);
            in_full_norm_request = (uu___111_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___111_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___112_1552 = fs  in
          {
            beta = (uu___112_1552.beta);
            iota = (uu___112_1552.iota);
            zeta = (uu___112_1552.zeta);
            weak = (uu___112_1552.weak);
            hnf = (uu___112_1552.hnf);
            primops = (uu___112_1552.primops);
            do_not_unfold_pure_lets = (uu___112_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1552.unfold_until);
            unfold_only = (uu___112_1552.unfold_only);
            unfold_fully = (uu___112_1552.unfold_fully);
            unfold_attr = (uu___112_1552.unfold_attr);
            unfold_tac = (uu___112_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1552.erase_universes);
            allow_unbound_universes = (uu___112_1552.allow_unbound_universes);
            reify_ = (uu___112_1552.reify_);
            compress_uvars = (uu___112_1552.compress_uvars);
            no_full_norm = (uu___112_1552.no_full_norm);
            check_no_uvars = (uu___112_1552.check_no_uvars);
            unmeta = (uu___112_1552.unmeta);
            unascribe = (uu___112_1552.unascribe);
            in_full_norm_request = (uu___112_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___113_1553 = fs  in
          {
            beta = (uu___113_1553.beta);
            iota = (uu___113_1553.iota);
            zeta = (uu___113_1553.zeta);
            weak = (uu___113_1553.weak);
            hnf = (uu___113_1553.hnf);
            primops = (uu___113_1553.primops);
            do_not_unfold_pure_lets = (uu___113_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1553.unfold_until);
            unfold_only = (uu___113_1553.unfold_only);
            unfold_fully = (uu___113_1553.unfold_fully);
            unfold_attr = (uu___113_1553.unfold_attr);
            unfold_tac = (uu___113_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1553.pure_subterms_within_computations);
            simplify = (uu___113_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1553.allow_unbound_universes);
            reify_ = (uu___113_1553.reify_);
            compress_uvars = (uu___113_1553.compress_uvars);
            no_full_norm = (uu___113_1553.no_full_norm);
            check_no_uvars = (uu___113_1553.check_no_uvars);
            unmeta = (uu___113_1553.unmeta);
            unascribe = (uu___113_1553.unascribe);
            in_full_norm_request = (uu___113_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___113_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1554 = fs  in
          {
            beta = (uu___114_1554.beta);
            iota = (uu___114_1554.iota);
            zeta = (uu___114_1554.zeta);
            weak = (uu___114_1554.weak);
            hnf = (uu___114_1554.hnf);
            primops = (uu___114_1554.primops);
            do_not_unfold_pure_lets = (uu___114_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1554.unfold_until);
            unfold_only = (uu___114_1554.unfold_only);
            unfold_fully = (uu___114_1554.unfold_fully);
            unfold_attr = (uu___114_1554.unfold_attr);
            unfold_tac = (uu___114_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1554.pure_subterms_within_computations);
            simplify = (uu___114_1554.simplify);
            erase_universes = (uu___114_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1554.reify_);
            compress_uvars = (uu___114_1554.compress_uvars);
            no_full_norm = (uu___114_1554.no_full_norm);
            check_no_uvars = (uu___114_1554.check_no_uvars);
            unmeta = (uu___114_1554.unmeta);
            unascribe = (uu___114_1554.unascribe);
            in_full_norm_request = (uu___114_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___115_1555 = fs  in
          {
            beta = (uu___115_1555.beta);
            iota = (uu___115_1555.iota);
            zeta = (uu___115_1555.zeta);
            weak = (uu___115_1555.weak);
            hnf = (uu___115_1555.hnf);
            primops = (uu___115_1555.primops);
            do_not_unfold_pure_lets = (uu___115_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1555.unfold_until);
            unfold_only = (uu___115_1555.unfold_only);
            unfold_fully = (uu___115_1555.unfold_fully);
            unfold_attr = (uu___115_1555.unfold_attr);
            unfold_tac = (uu___115_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1555.pure_subterms_within_computations);
            simplify = (uu___115_1555.simplify);
            erase_universes = (uu___115_1555.erase_universes);
            allow_unbound_universes = (uu___115_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1555.compress_uvars);
            no_full_norm = (uu___115_1555.no_full_norm);
            check_no_uvars = (uu___115_1555.check_no_uvars);
            unmeta = (uu___115_1555.unmeta);
            unascribe = (uu___115_1555.unascribe);
            in_full_norm_request = (uu___115_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___115_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___116_1556 = fs  in
          {
            beta = (uu___116_1556.beta);
            iota = (uu___116_1556.iota);
            zeta = (uu___116_1556.zeta);
            weak = (uu___116_1556.weak);
            hnf = (uu___116_1556.hnf);
            primops = (uu___116_1556.primops);
            do_not_unfold_pure_lets = (uu___116_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1556.unfold_until);
            unfold_only = (uu___116_1556.unfold_only);
            unfold_fully = (uu___116_1556.unfold_fully);
            unfold_attr = (uu___116_1556.unfold_attr);
            unfold_tac = (uu___116_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1556.pure_subterms_within_computations);
            simplify = (uu___116_1556.simplify);
            erase_universes = (uu___116_1556.erase_universes);
            allow_unbound_universes = (uu___116_1556.allow_unbound_universes);
            reify_ = (uu___116_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1556.no_full_norm);
            check_no_uvars = (uu___116_1556.check_no_uvars);
            unmeta = (uu___116_1556.unmeta);
            unascribe = (uu___116_1556.unascribe);
            in_full_norm_request = (uu___116_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___116_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___117_1557 = fs  in
          {
            beta = (uu___117_1557.beta);
            iota = (uu___117_1557.iota);
            zeta = (uu___117_1557.zeta);
            weak = (uu___117_1557.weak);
            hnf = (uu___117_1557.hnf);
            primops = (uu___117_1557.primops);
            do_not_unfold_pure_lets = (uu___117_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1557.unfold_until);
            unfold_only = (uu___117_1557.unfold_only);
            unfold_fully = (uu___117_1557.unfold_fully);
            unfold_attr = (uu___117_1557.unfold_attr);
            unfold_tac = (uu___117_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1557.pure_subterms_within_computations);
            simplify = (uu___117_1557.simplify);
            erase_universes = (uu___117_1557.erase_universes);
            allow_unbound_universes = (uu___117_1557.allow_unbound_universes);
            reify_ = (uu___117_1557.reify_);
            compress_uvars = (uu___117_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1557.check_no_uvars);
            unmeta = (uu___117_1557.unmeta);
            unascribe = (uu___117_1557.unascribe);
            in_full_norm_request = (uu___117_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___118_1558 = fs  in
          {
            beta = (uu___118_1558.beta);
            iota = (uu___118_1558.iota);
            zeta = (uu___118_1558.zeta);
            weak = (uu___118_1558.weak);
            hnf = (uu___118_1558.hnf);
            primops = (uu___118_1558.primops);
            do_not_unfold_pure_lets = (uu___118_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1558.unfold_until);
            unfold_only = (uu___118_1558.unfold_only);
            unfold_fully = (uu___118_1558.unfold_fully);
            unfold_attr = (uu___118_1558.unfold_attr);
            unfold_tac = (uu___118_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1558.pure_subterms_within_computations);
            simplify = (uu___118_1558.simplify);
            erase_universes = (uu___118_1558.erase_universes);
            allow_unbound_universes = (uu___118_1558.allow_unbound_universes);
            reify_ = (uu___118_1558.reify_);
            compress_uvars = (uu___118_1558.compress_uvars);
            no_full_norm = (uu___118_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1558.unmeta);
            unascribe = (uu___118_1558.unascribe);
            in_full_norm_request = (uu___118_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___119_1559 = fs  in
          {
            beta = (uu___119_1559.beta);
            iota = (uu___119_1559.iota);
            zeta = (uu___119_1559.zeta);
            weak = (uu___119_1559.weak);
            hnf = (uu___119_1559.hnf);
            primops = (uu___119_1559.primops);
            do_not_unfold_pure_lets = (uu___119_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1559.unfold_until);
            unfold_only = (uu___119_1559.unfold_only);
            unfold_fully = (uu___119_1559.unfold_fully);
            unfold_attr = (uu___119_1559.unfold_attr);
            unfold_tac = (uu___119_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1559.pure_subterms_within_computations);
            simplify = (uu___119_1559.simplify);
            erase_universes = (uu___119_1559.erase_universes);
            allow_unbound_universes = (uu___119_1559.allow_unbound_universes);
            reify_ = (uu___119_1559.reify_);
            compress_uvars = (uu___119_1559.compress_uvars);
            no_full_norm = (uu___119_1559.no_full_norm);
            check_no_uvars = (uu___119_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1559.unascribe);
            in_full_norm_request = (uu___119_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___119_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___120_1560 = fs  in
          {
            beta = (uu___120_1560.beta);
            iota = (uu___120_1560.iota);
            zeta = (uu___120_1560.zeta);
            weak = (uu___120_1560.weak);
            hnf = (uu___120_1560.hnf);
            primops = (uu___120_1560.primops);
            do_not_unfold_pure_lets = (uu___120_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1560.unfold_until);
            unfold_only = (uu___120_1560.unfold_only);
            unfold_fully = (uu___120_1560.unfold_fully);
            unfold_attr = (uu___120_1560.unfold_attr);
            unfold_tac = (uu___120_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1560.pure_subterms_within_computations);
            simplify = (uu___120_1560.simplify);
            erase_universes = (uu___120_1560.erase_universes);
            allow_unbound_universes = (uu___120_1560.allow_unbound_universes);
            reify_ = (uu___120_1560.reify_);
            compress_uvars = (uu___120_1560.compress_uvars);
            no_full_norm = (uu___120_1560.no_full_norm);
            check_no_uvars = (uu___120_1560.check_no_uvars);
            unmeta = (uu___120_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1560.weakly_reduce_scrutinee)
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1613  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1902 -> false
  
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
    match projectee with | Univ _0 -> true | uu____2006 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____2019 -> false
  
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
  primitive_steps: primitive_step FStar_Util.smap ;
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
  cfg -> primitive_step FStar_Util.smap) =
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
  primitive_step FStar_Util.smap ->
    primitive_step Prims.list -> primitive_step FStar_Util.smap)
  =
  fun m  ->
    fun l  ->
      FStar_List.iter
        (fun p  ->
           let uu____2346 = FStar_Ident.text_of_lid p.name  in
           FStar_Util.smap_add m uu____2346 p) l;
      m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.smap) =
  fun l  ->
    let uu____2360 = FStar_Util.smap_create (Prims.parse_int "101")  in
    add_steps uu____2360 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2375 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.smap_try_find cfg.primitive_steps uu____2375
  
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
    match projectee with | Arg _0 -> true | uu____2533 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2571 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2609 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2682 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2732 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2790 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2834 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2874 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2912 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2930 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2957 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2957 with | (hd1,uu____2971) -> hd1
  
let mk :
  'Auu____2994 .
    'Auu____2994 ->
      FStar_Range.range -> 'Auu____2994 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3057 = FStar_ST.op_Bang r  in
          match uu____3057 with
          | FStar_Pervasives_Native.Some uu____3109 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3185 =
      FStar_List.map
        (fun uu____3199  ->
           match uu____3199 with
           | (bopt,c) ->
               let uu____3212 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3214 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3212 uu____3214) env
       in
    FStar_All.pipe_right uu____3185 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_3217  ->
    match uu___79_3217 with
    | Clos (env,t,uu____3220,uu____3221) ->
        let uu____3266 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3273 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3266 uu____3273
    | Univ uu____3274 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_3279  ->
    match uu___80_3279 with
    | Arg (c,uu____3281,uu____3282) ->
        let uu____3283 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3283
    | MemoLazy uu____3284 -> "MemoLazy"
    | Abs (uu____3291,bs,uu____3293,uu____3294,uu____3295) ->
        let uu____3300 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3300
    | UnivArgs uu____3305 -> "UnivArgs"
    | Match uu____3312 -> "Match"
    | App (uu____3321,t,uu____3323,uu____3324) ->
        let uu____3325 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3325
    | Meta (uu____3326,m,uu____3328) -> "Meta"
    | Let uu____3329 -> "Let"
    | Cfg uu____3338 -> "Cfg"
    | Debug (t,uu____3340) ->
        let uu____3341 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3341
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3351 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3351 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3392 . 'Auu____3392 Prims.list -> Prims.bool =
  fun uu___81_3399  ->
    match uu___81_3399 with | [] -> true | uu____3402 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3434 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3434
      with
      | uu____3453 ->
          let uu____3454 =
            let uu____3455 = FStar_Syntax_Print.db_to_string x  in
            let uu____3456 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3455
              uu____3456
             in
          failwith uu____3454
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3464 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3464
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3468 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3468
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3472 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3472
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
          let uu____3506 =
            FStar_List.fold_left
              (fun uu____3532  ->
                 fun u1  ->
                   match uu____3532 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3557 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3557 with
                        | (k_u,n1) ->
                            let uu____3572 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3572
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3506 with
          | (uu____3590,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3617 =
                   let uu____3618 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3618  in
                 match uu____3617 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3636 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3644 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3650 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3659 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3668 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3675 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3675 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3692 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3692 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3700 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3708 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3708 with
                                  | (uu____3713,m) -> n1 <= m))
                           in
                        if uu____3700 then rest1 else us1
                    | uu____3718 -> us1)
               | uu____3723 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3727 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3727
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3731 = aux u  in
           match uu____3731 with
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
            (fun uu____3877  ->
               let uu____3878 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3879 = env_to_string env  in
               let uu____3880 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3878 uu____3879 uu____3880);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3889 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3892 ->
                    let uu____3917 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3917
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3918 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3919 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3920 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3921 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3922 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3944 ->
                           let uu____3961 =
                             let uu____3962 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3963 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3962 uu____3963
                              in
                           failwith uu____3961
                       | uu____3966 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3972 =
                        let uu____3973 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3973  in
                      mk uu____3972 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3981 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3981  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3983 = lookup_bvar env x  in
                    (match uu____3983 with
                     | Univ uu____3986 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___125_3990 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___125_3990.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___125_3990.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3996,uu____3997) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4082  ->
                              fun stack1  ->
                                match uu____4082 with
                                | (a,aq) ->
                                    let uu____4094 =
                                      let uu____4095 =
                                        let uu____4102 =
                                          let uu____4103 =
                                            let uu____4134 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4134, false)  in
                                          Clos uu____4103  in
                                        (uu____4102, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4095  in
                                    uu____4094 :: stack1) args)
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
                    let uu____4328 = close_binders cfg env bs  in
                    (match uu____4328 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4375 =
                      let uu____4386 =
                        let uu____4393 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4393]  in
                      close_binders cfg env uu____4386  in
                    (match uu____4375 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4416 =
                             let uu____4417 =
                               let uu____4424 =
                                 let uu____4425 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4425
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4424, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4417  in
                           mk uu____4416 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4516 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4516
                      | FStar_Util.Inr c ->
                          let uu____4530 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4530
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4549 =
                        let uu____4550 =
                          let uu____4577 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4577, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4550  in
                      mk uu____4549 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4623 =
                            let uu____4624 =
                              let uu____4631 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4631, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4624  in
                          mk uu____4623 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4683  -> dummy :: env1) env
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
                    let uu____4704 =
                      let uu____4715 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4715
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4734 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___126_4750 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_4750.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_4750.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4734))
                       in
                    (match uu____4704 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___127_4768 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_4768.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_4768.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_4768.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_4768.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4782,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4845  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4870 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4870
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4890  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4914 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4914
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___128_4922 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4922.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4922.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___129_4923 = lb  in
                      let uu____4924 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___129_4923.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___129_4923.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4924;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___129_4923.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___129_4923.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4956  -> fun env1  -> dummy :: env1)
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
            (fun uu____5059  ->
               let uu____5060 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5061 = env_to_string env  in
               let uu____5062 = stack_to_string stack  in
               let uu____5063 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5060 uu____5061 uu____5062 uu____5063);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5068,uu____5069),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5144 = close_binders cfg env' bs  in
               (match uu____5144 with
                | (bs1,uu____5158) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5174 =
                      let uu___130_5175 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___130_5175.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___130_5175.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5174)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5221 =
                 match uu____5221 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5296 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5317 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5377  ->
                                     fun uu____5378  ->
                                       match (uu____5377, uu____5378) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5469 = norm_pat env4 p1
                                              in
                                           (match uu____5469 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5317 with
                            | (pats1,env4) ->
                                ((let uu___131_5551 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___131_5551.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___132_5570 = x  in
                             let uu____5571 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___132_5570.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___132_5570.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5571
                             }  in
                           ((let uu___133_5585 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___133_5585.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___134_5596 = x  in
                             let uu____5597 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5596.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5596.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5597
                             }  in
                           ((let uu___135_5611 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5611.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___136_5627 = x  in
                             let uu____5628 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5627.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5627.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5628
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___137_5637 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5637.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5642 = norm_pat env2 pat  in
                     (match uu____5642 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5687 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5687
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5706 =
                   let uu____5707 =
                     let uu____5730 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5730)  in
                   FStar_Syntax_Syntax.Tm_match uu____5707  in
                 mk uu____5706 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5825 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5914  ->
                                       match uu____5914 with
                                       | (a,q) ->
                                           let uu____5933 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5933, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5825
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5944 =
                       let uu____5951 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5951)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5944
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5963 =
                       let uu____5972 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5972)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5963
                 | uu____5977 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5981 -> failwith "Impossible: unexpected stack element")

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
        let uu____5995 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6044  ->
                  fun uu____6045  ->
                    match (uu____6044, uu____6045) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_6115 = b  in
                          let uu____6116 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_6115.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_6115.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6116
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5995 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6209 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6222 = inline_closure_env cfg env [] t  in
                 let uu____6223 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6222 uu____6223
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6236 = inline_closure_env cfg env [] t  in
                 let uu____6237 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6236 uu____6237
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6283  ->
                           match uu____6283 with
                           | (a,q) ->
                               let uu____6296 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6296, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_6311  ->
                           match uu___82_6311 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6315 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6315
                           | f -> f))
                    in
                 let uu____6319 =
                   let uu___139_6320 = c1  in
                   let uu____6321 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6321;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_6320.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6319)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_6331  ->
            match uu___83_6331 with
            | FStar_Syntax_Syntax.DECREASES uu____6332 -> false
            | uu____6335 -> true))

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
                   (fun uu___84_6353  ->
                      match uu___84_6353 with
                      | FStar_Syntax_Syntax.DECREASES uu____6354 -> false
                      | uu____6357 -> true))
               in
            let rc1 =
              let uu___140_6359 = rc  in
              let uu____6360 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_6359.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6360;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6369 -> lopt

let (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let (built_in_primitive_steps : primitive_step FStar_Util.smap) =
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
    let uu____6482 =
      let uu____6491 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6491  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6482  in
  let arg_as_bounded_int uu____6517 =
    match uu____6517 with
    | (a,uu____6529) ->
        let uu____6536 =
          let uu____6537 = FStar_Syntax_Subst.compress a  in
          uu____6537.FStar_Syntax_Syntax.n  in
        (match uu____6536 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6547;
                FStar_Syntax_Syntax.vars = uu____6548;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6550;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6551;_},uu____6552)::[])
             when
             let uu____6591 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6591 "int_to_t" ->
             let uu____6592 =
               let uu____6597 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6597)  in
             FStar_Pervasives_Native.Some uu____6592
         | uu____6602 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6650 = f a  in FStar_Pervasives_Native.Some uu____6650
    | uu____6651 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6707 = f a0 a1  in FStar_Pervasives_Native.Some uu____6707
    | uu____6708 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6766 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6766  in
  let binary_op as_a f res args =
    let uu____6831 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6831  in
  let as_primitive_step is_strong uu____6862 =
    match uu____6862 with
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
           let uu____6922 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6922)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6958 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6958)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____6987 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____6987)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7023 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7023)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7059 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7059)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7191 =
          let uu____7200 = as_a a  in
          let uu____7203 = as_b b  in (uu____7200, uu____7203)  in
        (match uu____7191 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7218 =
               let uu____7219 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7219  in
             FStar_Pervasives_Native.Some uu____7218
         | uu____7220 -> FStar_Pervasives_Native.None)
    | uu____7229 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7249 =
        let uu____7250 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7250  in
      mk uu____7249 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7262 =
      let uu____7265 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7265  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7262  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7307 =
      let uu____7308 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7308  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7307
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7330 = arg_as_string a1  in
        (match uu____7330 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7336 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7336 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7349 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7349
              | uu____7350 -> FStar_Pervasives_Native.None)
         | uu____7355 -> FStar_Pervasives_Native.None)
    | uu____7358 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7372 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7372
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7409 =
          let uu____7430 = arg_as_string fn  in
          let uu____7433 = arg_as_int from_line  in
          let uu____7436 = arg_as_int from_col  in
          let uu____7439 = arg_as_int to_line  in
          let uu____7442 = arg_as_int to_col  in
          (uu____7430, uu____7433, uu____7436, uu____7439, uu____7442)  in
        (match uu____7409 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7473 =
                 let uu____7474 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7475 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7474 uu____7475  in
               let uu____7476 =
                 let uu____7477 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7478 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7477 uu____7478  in
               FStar_Range.mk_range fn1 uu____7473 uu____7476  in
             let uu____7479 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7479
         | uu____7480 -> FStar_Pervasives_Native.None)
    | uu____7501 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7534)::(a1,uu____7536)::(a2,uu____7538)::[] ->
        let uu____7575 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7575 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7588 -> FStar_Pervasives_Native.None)
    | uu____7589 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7620)::[] ->
        let uu____7629 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7629 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7635 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7635
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7636 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7662 =
      let uu____7679 =
        let uu____7696 =
          let uu____7713 =
            let uu____7730 =
              let uu____7747 =
                let uu____7764 =
                  let uu____7781 =
                    let uu____7798 =
                      let uu____7815 =
                        let uu____7832 =
                          let uu____7849 =
                            let uu____7866 =
                              let uu____7883 =
                                let uu____7900 =
                                  let uu____7917 =
                                    let uu____7934 =
                                      let uu____7951 =
                                        let uu____7968 =
                                          let uu____7985 =
                                            let uu____8002 =
                                              let uu____8019 =
                                                let uu____8034 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8034,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8043 =
                                                let uu____8060 =
                                                  let uu____8075 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8075,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8088 =
                                                  let uu____8105 =
                                                    let uu____8122 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8122,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8133 =
                                                    let uu____8152 =
                                                      let uu____8169 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8169,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8152]  in
                                                  uu____8105 :: uu____8133
                                                   in
                                                uu____8060 :: uu____8088  in
                                              uu____8019 :: uu____8043  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8002
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7985
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7968
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7951
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7934
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8397 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8397 y)))
                                    :: uu____7917
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7900
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7883
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7866
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7849
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7832
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7815
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8592 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8592)))
                      :: uu____7798
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8622 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8622)))
                    :: uu____7781
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8652 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8652)))
                  :: uu____7764
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8682 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8682)))
                :: uu____7747
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7730
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7713
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7696
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7679
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7662
     in
  let weak_ops =
    let uu____8843 =
      let uu____8864 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8864, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8843]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8962 =
        let uu____8967 =
          let uu____8968 = FStar_Syntax_Syntax.as_arg c  in [uu____8968]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8967  in
      uu____8962 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9024 =
                let uu____9039 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9039, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9061  ->
                          fun uu____9062  ->
                            match (uu____9061, uu____9062) with
                            | ((int_to_t1,x),(uu____9081,y)) ->
                                let uu____9091 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9091)))
                 in
              let uu____9092 =
                let uu____9109 =
                  let uu____9124 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9124, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9146  ->
                            fun uu____9147  ->
                              match (uu____9146, uu____9147) with
                              | ((int_to_t1,x),(uu____9166,y)) ->
                                  let uu____9176 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9176)))
                   in
                let uu____9177 =
                  let uu____9194 =
                    let uu____9209 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9209, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9231  ->
                              fun uu____9232  ->
                                match (uu____9231, uu____9232) with
                                | ((int_to_t1,x),(uu____9251,y)) ->
                                    let uu____9261 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9261)))
                     in
                  let uu____9262 =
                    let uu____9279 =
                      let uu____9294 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9294, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9312  ->
                                match uu____9312 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9279]  in
                  uu____9194 :: uu____9262  in
                uu____9109 :: uu____9177  in
              uu____9024 :: uu____9092))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9442 =
                let uu____9457 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9457, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9479  ->
                          fun uu____9480  ->
                            match (uu____9479, uu____9480) with
                            | ((int_to_t1,x),(uu____9499,y)) ->
                                let uu____9509 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9509)))
                 in
              let uu____9510 =
                let uu____9527 =
                  let uu____9542 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9542, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9564  ->
                            fun uu____9565  ->
                              match (uu____9564, uu____9565) with
                              | ((int_to_t1,x),(uu____9584,y)) ->
                                  let uu____9594 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9594)))
                   in
                [uu____9527]  in
              uu____9442 :: uu____9510))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.smap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____9724)::(a1,uu____9726)::(a2,uu____9728)::[] ->
        let uu____9765 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9765 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9771 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9771.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9771.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9775 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9775.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9775.FStar_Syntax_Syntax.vars)
                })
         | uu____9776 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9778)::uu____9779::(a1,uu____9781)::(a2,uu____9783)::[] ->
        let uu____9832 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9832 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9838 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9838.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9838.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9842 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9842.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9842.FStar_Syntax_Syntax.vars)
                })
         | uu____9843 -> FStar_Pervasives_Native.None)
    | uu____9844 -> failwith "Unexpected number of arguments"  in
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
    let uu____9898 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9898 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9950 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9950) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10012  ->
           fun subst1  ->
             match uu____10012 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10053,uu____10054)) ->
                      let uu____10113 = b  in
                      (match uu____10113 with
                       | (bv,uu____10121) ->
                           let uu____10122 =
                             let uu____10123 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10123  in
                           if uu____10122
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10128 = unembed_binder term1  in
                              match uu____10128 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10135 =
                                      let uu___143_10136 = bv  in
                                      let uu____10137 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_10136.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_10136.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10137
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10135
                                     in
                                  let b_for_x =
                                    let uu____10141 =
                                      let uu____10148 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10148)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10141  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_10158  ->
                                         match uu___85_10158 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10159,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10161;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10162;_})
                                             ->
                                             let uu____10167 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10167
                                         | uu____10168 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10169 -> subst1)) env []
  
let reduce_primops :
  'Auu____10192 'Auu____10193 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10192) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10193 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10239 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10239 with
             | (head1,args) ->
                 let uu____10276 =
                   let uu____10277 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10277.FStar_Syntax_Syntax.n  in
                 (match uu____10276 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10281 = find_prim_step cfg fv  in
                      (match uu____10281 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10303  ->
                                   let uu____10304 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10305 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10312 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10304 uu____10305 uu____10312);
                              tm)
                           else
                             (let uu____10314 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10314 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10425  ->
                                        let uu____10426 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10426);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10429  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10431 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10431 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10437  ->
                                              let uu____10438 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10438);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10444  ->
                                              let uu____10445 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10446 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10445 uu____10446);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10447 ->
                           (log_primops cfg
                              (fun uu____10451  ->
                                 let uu____10452 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10452);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10456  ->
                            let uu____10457 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10457);
                       (match args with
                        | (a1,uu____10459)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10476 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10488  ->
                            let uu____10489 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10489);
                       (match args with
                        | (t,uu____10491)::(r,uu____10493)::[] ->
                            let uu____10520 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10520 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___144_10524 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___144_10524.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___144_10524.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10527 -> tm))
                  | uu____10536 -> tm))
  
let reduce_equality :
  'Auu____10547 'Auu____10548 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10547) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10548 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_10592 = cfg  in
         {
           steps =
             (let uu___146_10595 = default_steps  in
              {
                beta = (uu___146_10595.beta);
                iota = (uu___146_10595.iota);
                zeta = (uu___146_10595.zeta);
                weak = (uu___146_10595.weak);
                hnf = (uu___146_10595.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_10595.do_not_unfold_pure_lets);
                unfold_until = (uu___146_10595.unfold_until);
                unfold_only = (uu___146_10595.unfold_only);
                unfold_fully = (uu___146_10595.unfold_fully);
                unfold_attr = (uu___146_10595.unfold_attr);
                unfold_tac = (uu___146_10595.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_10595.pure_subterms_within_computations);
                simplify = (uu___146_10595.simplify);
                erase_universes = (uu___146_10595.erase_universes);
                allow_unbound_universes =
                  (uu___146_10595.allow_unbound_universes);
                reify_ = (uu___146_10595.reify_);
                compress_uvars = (uu___146_10595.compress_uvars);
                no_full_norm = (uu___146_10595.no_full_norm);
                check_no_uvars = (uu___146_10595.check_no_uvars);
                unmeta = (uu___146_10595.unmeta);
                unascribe = (uu___146_10595.unascribe);
                in_full_norm_request = (uu___146_10595.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___146_10595.weakly_reduce_scrutinee)
              });
           tcenv = (uu___145_10592.tcenv);
           debug = (uu___145_10592.debug);
           delta_level = (uu___145_10592.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_10592.strong);
           memoize_lazy = (uu___145_10592.memoize_lazy);
           normalize_pure_lets = (uu___145_10592.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10602 .
    FStar_Syntax_Syntax.term -> 'Auu____10602 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10617 =
        let uu____10624 =
          let uu____10625 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10625.FStar_Syntax_Syntax.n  in
        (uu____10624, args)  in
      match uu____10617 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10631::uu____10632::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10636::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10641::uu____10642::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10645 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_10658  ->
    match uu___86_10658 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10664 =
          let uu____10667 =
            let uu____10668 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10668  in
          [uu____10667]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10664
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10674 =
          let uu____10677 =
            let uu____10678 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10678  in
          [uu____10677]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10674
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10699 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10699) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10745 =
          let uu____10750 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10750 s  in
        match uu____10745 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10766 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10766
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10783::(tm,uu____10785)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10814)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10835)::uu____10836::(tm,uu____10838)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10879 =
            let uu____10884 = full_norm steps  in parse_steps uu____10884  in
          (match uu____10879 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10923 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_10942  ->
    match uu___87_10942 with
    | (App
        (uu____10945,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10946;
                       FStar_Syntax_Syntax.vars = uu____10947;_},uu____10948,uu____10949))::uu____10950
        -> true
    | uu____10957 -> false
  
let firstn :
  'Auu____10966 .
    Prims.int ->
      'Auu____10966 Prims.list ->
        ('Auu____10966 Prims.list,'Auu____10966 Prims.list)
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
          (uu____11008,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11009;
                         FStar_Syntax_Syntax.vars = uu____11010;_},uu____11011,uu____11012))::uu____11013
          -> (cfg.steps).reify_
      | uu____11020 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11043) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11053) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11072  ->
                  match uu____11072 with
                  | (a,uu____11080) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11086 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11111 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11112 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11129 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11130 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11131 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11132 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11133 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11134 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11141 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11148 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11161 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11178 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11191 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11198 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11260  ->
                   match uu____11260 with
                   | (a,uu____11268) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11275) ->
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
                     (fun uu____11397  ->
                        match uu____11397 with
                        | (a,uu____11405) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11410,uu____11411,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11417,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11423 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11430 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11431 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11723 ->
                   let uu____11748 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11748
               | uu____11749 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11757  ->
               let uu____11758 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11759 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11760 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11767 =
                 let uu____11768 =
                   let uu____11771 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11771
                    in
                 stack_to_string uu____11768  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11758 uu____11759 uu____11760 uu____11767);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11794 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11795 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11796 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11797;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_18;
                 FStar_Syntax_Syntax.fv_qual = uu____11798;_}
               when _0_18 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11801;
                 FStar_Syntax_Syntax.fv_delta = uu____11802;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11803;
                 FStar_Syntax_Syntax.fv_delta = uu____11804;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11805);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11812 ->
               let uu____11819 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11819
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11849 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11849)
               ->
               let cfg' =
                 let uu___147_11851 = cfg  in
                 {
                   steps =
                     (let uu___148_11854 = cfg.steps  in
                      {
                        beta = (uu___148_11854.beta);
                        iota = (uu___148_11854.iota);
                        zeta = (uu___148_11854.zeta);
                        weak = (uu___148_11854.weak);
                        hnf = (uu___148_11854.hnf);
                        primops = (uu___148_11854.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_11854.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_11854.unfold_attr);
                        unfold_tac = (uu___148_11854.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_11854.pure_subterms_within_computations);
                        simplify = (uu___148_11854.simplify);
                        erase_universes = (uu___148_11854.erase_universes);
                        allow_unbound_universes =
                          (uu___148_11854.allow_unbound_universes);
                        reify_ = (uu___148_11854.reify_);
                        compress_uvars = (uu___148_11854.compress_uvars);
                        no_full_norm = (uu___148_11854.no_full_norm);
                        check_no_uvars = (uu___148_11854.check_no_uvars);
                        unmeta = (uu___148_11854.unmeta);
                        unascribe = (uu___148_11854.unascribe);
                        in_full_norm_request =
                          (uu___148_11854.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___148_11854.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___147_11851.tcenv);
                   debug = (uu___147_11851.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___147_11851.primitive_steps);
                   strong = (uu___147_11851.strong);
                   memoize_lazy = (uu___147_11851.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11859 = get_norm_request (norm cfg' env []) args  in
               (match uu____11859 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11890  ->
                              fun stack1  ->
                                match uu____11890 with
                                | (a,aq) ->
                                    let uu____11902 =
                                      let uu____11903 =
                                        let uu____11910 =
                                          let uu____11911 =
                                            let uu____11942 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11942, false)  in
                                          Clos uu____11911  in
                                        (uu____11910, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11903  in
                                    uu____11902 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12026  ->
                          let uu____12027 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12027);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12049 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_12054  ->
                                match uu___88_12054 with
                                | UnfoldUntil uu____12055 -> true
                                | UnfoldOnly uu____12056 -> true
                                | UnfoldFully uu____12059 -> true
                                | uu____12062 -> false))
                         in
                      if uu____12049
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_12067 = cfg  in
                      let uu____12068 =
                        let uu___150_12069 = to_fsteps s  in
                        {
                          beta = (uu___150_12069.beta);
                          iota = (uu___150_12069.iota);
                          zeta = (uu___150_12069.zeta);
                          weak = (uu___150_12069.weak);
                          hnf = (uu___150_12069.hnf);
                          primops = (uu___150_12069.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_12069.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_12069.unfold_until);
                          unfold_only = (uu___150_12069.unfold_only);
                          unfold_fully = (uu___150_12069.unfold_fully);
                          unfold_attr = (uu___150_12069.unfold_attr);
                          unfold_tac = (uu___150_12069.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_12069.pure_subterms_within_computations);
                          simplify = (uu___150_12069.simplify);
                          erase_universes = (uu___150_12069.erase_universes);
                          allow_unbound_universes =
                            (uu___150_12069.allow_unbound_universes);
                          reify_ = (uu___150_12069.reify_);
                          compress_uvars = (uu___150_12069.compress_uvars);
                          no_full_norm = (uu___150_12069.no_full_norm);
                          check_no_uvars = (uu___150_12069.check_no_uvars);
                          unmeta = (uu___150_12069.unmeta);
                          unascribe = (uu___150_12069.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___150_12069.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12068;
                        tcenv = (uu___149_12067.tcenv);
                        debug = (uu___149_12067.debug);
                        delta_level;
                        primitive_steps = (uu___149_12067.primitive_steps);
                        strong = (uu___149_12067.strong);
                        memoize_lazy = (uu___149_12067.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12078 =
                          let uu____12079 =
                            let uu____12084 = FStar_Util.now ()  in
                            (t1, uu____12084)  in
                          Debug uu____12079  in
                        uu____12078 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12088 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12088
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12097 =
                      let uu____12104 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12104, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12097  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12114 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12114  in
               let uu____12115 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12115
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12121  ->
                       let uu____12122 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12123 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12122 uu____12123);
                  if b
                  then
                    (let uu____12124 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12124 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12132 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12132) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12145),uu____12146);
                                FStar_Syntax_Syntax.sigrng = uu____12147;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12149;
                                FStar_Syntax_Syntax.sigattrs = uu____12150;_},uu____12151),uu____12152)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12217 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_12221  ->
                               match uu___89_12221 with
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
                          (let uu____12231 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12231))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12250) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12285,uu____12286) -> false)))
                     in
                  let uu____12303 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12319 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12319 then (true, true) else (false, false)
                     in
                  match uu____12303 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12332  ->
                            let uu____12333 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12334 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12335 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12333 uu____12334 uu____12335);
                       if should_delta2
                       then
                         (let uu____12336 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_12352 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_12355 = cfg.steps  in
                                      {
                                        beta = (uu___152_12355.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_12355.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_12355.unfold_attr);
                                        unfold_tac =
                                          (uu___152_12355.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_12355.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_12355.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_12355.allow_unbound_universes);
                                        reify_ = (uu___152_12355.reify_);
                                        compress_uvars =
                                          (uu___152_12355.compress_uvars);
                                        no_full_norm =
                                          (uu___152_12355.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_12355.check_no_uvars);
                                        unmeta = (uu___152_12355.unmeta);
                                        unascribe =
                                          (uu___152_12355.unascribe);
                                        in_full_norm_request =
                                          (uu___152_12355.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___152_12355.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___151_12352.tcenv);
                                   debug = (uu___151_12352.debug);
                                   delta_level = (uu___151_12352.delta_level);
                                   primitive_steps =
                                     (uu___151_12352.primitive_steps);
                                   strong = (uu___151_12352.strong);
                                   memoize_lazy =
                                     (uu___151_12352.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_12352.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12336 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12369 = lookup_bvar env x  in
               (match uu____12369 with
                | Univ uu____12370 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12419 = FStar_ST.op_Bang r  in
                      (match uu____12419 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12541  ->
                                 let uu____12542 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12543 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12542
                                   uu____12543);
                            (let uu____12544 = maybe_weakly_reduced t'  in
                             if uu____12544
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12545 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12616)::uu____12617 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12626)::uu____12627 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12639,uu____12640))::stack_rest ->
                    (match c with
                     | Univ uu____12644 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12653 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12674  ->
                                    let uu____12675 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12675);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12715  ->
                                    let uu____12716 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12716);
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
                       (fun uu____12794  ->
                          let uu____12795 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12795);
                     norm cfg env stack1 t1)
                | (Debug uu____12796)::uu____12797 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12807 = cfg.steps  in
                             {
                               beta = (uu___153_12807.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12807.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12807.unfold_until);
                               unfold_only = (uu___153_12807.unfold_only);
                               unfold_fully = (uu___153_12807.unfold_fully);
                               unfold_attr = (uu___153_12807.unfold_attr);
                               unfold_tac = (uu___153_12807.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12807.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12807.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12807.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12807.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12807.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12807.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12809 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12809.tcenv);
                               debug = (uu___154_12809.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12809.primitive_steps);
                               strong = (uu___154_12809.strong);
                               memoize_lazy = (uu___154_12809.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12809.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12811 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12811 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12853  -> dummy :: env1) env)
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
                                          let uu____12890 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12890)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12895 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12895.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12895.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12896 -> lopt  in
                           (log cfg
                              (fun uu____12902  ->
                                 let uu____12903 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12903);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12912 = cfg  in
                               {
                                 steps = (uu___156_12912.steps);
                                 tcenv = (uu___156_12912.tcenv);
                                 debug = (uu___156_12912.debug);
                                 delta_level = (uu___156_12912.delta_level);
                                 primitive_steps =
                                   (uu___156_12912.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12912.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12912.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12923)::uu____12924 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12936 = cfg.steps  in
                             {
                               beta = (uu___153_12936.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12936.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12936.unfold_until);
                               unfold_only = (uu___153_12936.unfold_only);
                               unfold_fully = (uu___153_12936.unfold_fully);
                               unfold_attr = (uu___153_12936.unfold_attr);
                               unfold_tac = (uu___153_12936.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12936.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12936.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12936.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12936.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12936.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12936.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12938 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12938.tcenv);
                               debug = (uu___154_12938.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12938.primitive_steps);
                               strong = (uu___154_12938.strong);
                               memoize_lazy = (uu___154_12938.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12938.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12940 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12940 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12982  -> dummy :: env1) env)
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
                                          let uu____13019 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13019)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13024 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13024.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13024.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13025 -> lopt  in
                           (log cfg
                              (fun uu____13031  ->
                                 let uu____13032 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13032);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13041 = cfg  in
                               {
                                 steps = (uu___156_13041.steps);
                                 tcenv = (uu___156_13041.tcenv);
                                 debug = (uu___156_13041.debug);
                                 delta_level = (uu___156_13041.delta_level);
                                 primitive_steps =
                                   (uu___156_13041.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13041.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13041.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13052)::uu____13053 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13067 = cfg.steps  in
                             {
                               beta = (uu___153_13067.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13067.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13067.unfold_until);
                               unfold_only = (uu___153_13067.unfold_only);
                               unfold_fully = (uu___153_13067.unfold_fully);
                               unfold_attr = (uu___153_13067.unfold_attr);
                               unfold_tac = (uu___153_13067.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13067.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13067.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13067.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13067.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13067.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13067.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13069 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13069.tcenv);
                               debug = (uu___154_13069.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13069.primitive_steps);
                               strong = (uu___154_13069.strong);
                               memoize_lazy = (uu___154_13069.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13069.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13071 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13071 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13113  -> dummy :: env1) env)
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
                                          let uu____13150 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13150)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13155 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13155.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13155.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13156 -> lopt  in
                           (log cfg
                              (fun uu____13162  ->
                                 let uu____13163 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13163);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13172 = cfg  in
                               {
                                 steps = (uu___156_13172.steps);
                                 tcenv = (uu___156_13172.tcenv);
                                 debug = (uu___156_13172.debug);
                                 delta_level = (uu___156_13172.delta_level);
                                 primitive_steps =
                                   (uu___156_13172.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13172.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13172.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13183)::uu____13184 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13198 = cfg.steps  in
                             {
                               beta = (uu___153_13198.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13198.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13198.unfold_until);
                               unfold_only = (uu___153_13198.unfold_only);
                               unfold_fully = (uu___153_13198.unfold_fully);
                               unfold_attr = (uu___153_13198.unfold_attr);
                               unfold_tac = (uu___153_13198.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13198.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13198.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13198.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13198.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13198.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13198.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13200 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13200.tcenv);
                               debug = (uu___154_13200.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13200.primitive_steps);
                               strong = (uu___154_13200.strong);
                               memoize_lazy = (uu___154_13200.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13200.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13202 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13202 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13244  -> dummy :: env1) env)
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
                                          let uu____13281 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13281)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13286 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13286.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13286.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13287 -> lopt  in
                           (log cfg
                              (fun uu____13293  ->
                                 let uu____13294 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13294);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13303 = cfg  in
                               {
                                 steps = (uu___156_13303.steps);
                                 tcenv = (uu___156_13303.tcenv);
                                 debug = (uu___156_13303.debug);
                                 delta_level = (uu___156_13303.delta_level);
                                 primitive_steps =
                                   (uu___156_13303.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13303.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13303.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13314)::uu____13315 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13333 = cfg.steps  in
                             {
                               beta = (uu___153_13333.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13333.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13333.unfold_until);
                               unfold_only = (uu___153_13333.unfold_only);
                               unfold_fully = (uu___153_13333.unfold_fully);
                               unfold_attr = (uu___153_13333.unfold_attr);
                               unfold_tac = (uu___153_13333.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13333.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13333.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13333.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13333.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13333.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13333.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13335 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13335.tcenv);
                               debug = (uu___154_13335.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13335.primitive_steps);
                               strong = (uu___154_13335.strong);
                               memoize_lazy = (uu___154_13335.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13335.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13337 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13337 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13379  -> dummy :: env1) env)
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
                                          let uu____13416 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13416)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13421 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13421.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13421.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13422 -> lopt  in
                           (log cfg
                              (fun uu____13428  ->
                                 let uu____13429 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13429);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13438 = cfg  in
                               {
                                 steps = (uu___156_13438.steps);
                                 tcenv = (uu___156_13438.tcenv);
                                 debug = (uu___156_13438.debug);
                                 delta_level = (uu___156_13438.delta_level);
                                 primitive_steps =
                                   (uu___156_13438.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13438.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13438.normalize_pure_lets)
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
                             let uu___153_13452 = cfg.steps  in
                             {
                               beta = (uu___153_13452.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13452.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13452.unfold_until);
                               unfold_only = (uu___153_13452.unfold_only);
                               unfold_fully = (uu___153_13452.unfold_fully);
                               unfold_attr = (uu___153_13452.unfold_attr);
                               unfold_tac = (uu___153_13452.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13452.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13452.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13452.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13452.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13452.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13452.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13454 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13454.tcenv);
                               debug = (uu___154_13454.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13454.primitive_steps);
                               strong = (uu___154_13454.strong);
                               memoize_lazy = (uu___154_13454.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13454.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13456 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13456 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13498  -> dummy :: env1) env)
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
                                          let uu____13535 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13535)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13540 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13540.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13540.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13541 -> lopt  in
                           (log cfg
                              (fun uu____13547  ->
                                 let uu____13548 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13548);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13557 = cfg  in
                               {
                                 steps = (uu___156_13557.steps);
                                 tcenv = (uu___156_13557.tcenv);
                                 debug = (uu___156_13557.debug);
                                 delta_level = (uu___156_13557.delta_level);
                                 primitive_steps =
                                   (uu___156_13557.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13557.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13557.normalize_pure_lets)
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
                      (fun uu____13606  ->
                         fun stack1  ->
                           match uu____13606 with
                           | (a,aq) ->
                               let uu____13618 =
                                 let uu____13619 =
                                   let uu____13626 =
                                     let uu____13627 =
                                       let uu____13658 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13658, false)  in
                                     Clos uu____13627  in
                                   (uu____13626, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13619  in
                               uu____13618 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13742  ->
                     let uu____13743 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13743);
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
                             ((let uu___157_13779 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_13779.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_13779.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13780 ->
                      let uu____13785 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13785)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13788 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13788 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13819 =
                          let uu____13820 =
                            let uu____13827 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_13829 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_13829.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_13829.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13827)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13820  in
                        mk uu____13819 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13848 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13848
               else
                 (let uu____13850 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13850 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13858 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13882  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13858 c1  in
                      let t2 =
                        let uu____13904 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13904 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14015)::uu____14016 ->
                    (log cfg
                       (fun uu____14029  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14030)::uu____14031 ->
                    (log cfg
                       (fun uu____14042  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14043,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14044;
                                   FStar_Syntax_Syntax.vars = uu____14045;_},uu____14046,uu____14047))::uu____14048
                    ->
                    (log cfg
                       (fun uu____14057  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14058)::uu____14059 ->
                    (log cfg
                       (fun uu____14070  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14071 ->
                    (log cfg
                       (fun uu____14074  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14078  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14095 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14095
                         | FStar_Util.Inr c ->
                             let uu____14103 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14103
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14116 =
                               let uu____14117 =
                                 let uu____14144 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14144, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14117
                                in
                             mk uu____14116 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14163 ->
                           let uu____14164 =
                             let uu____14165 =
                               let uu____14166 =
                                 let uu____14193 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14193, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14166
                                in
                             mk uu____14165 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14164))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___159_14270 = cfg  in
                   {
                     steps =
                       (let uu___160_14273 = cfg.steps  in
                        {
                          beta = (uu___160_14273.beta);
                          iota = (uu___160_14273.iota);
                          zeta = (uu___160_14273.zeta);
                          weak = true;
                          hnf = (uu___160_14273.hnf);
                          primops = (uu___160_14273.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_14273.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_14273.unfold_until);
                          unfold_only = (uu___160_14273.unfold_only);
                          unfold_fully = (uu___160_14273.unfold_fully);
                          unfold_attr = (uu___160_14273.unfold_attr);
                          unfold_tac = (uu___160_14273.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_14273.pure_subterms_within_computations);
                          simplify = (uu___160_14273.simplify);
                          erase_universes = (uu___160_14273.erase_universes);
                          allow_unbound_universes =
                            (uu___160_14273.allow_unbound_universes);
                          reify_ = (uu___160_14273.reify_);
                          compress_uvars = (uu___160_14273.compress_uvars);
                          no_full_norm = (uu___160_14273.no_full_norm);
                          check_no_uvars = (uu___160_14273.check_no_uvars);
                          unmeta = (uu___160_14273.unmeta);
                          unascribe = (uu___160_14273.unascribe);
                          in_full_norm_request =
                            (uu___160_14273.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___160_14273.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___159_14270.tcenv);
                     debug = (uu___159_14270.debug);
                     delta_level = (uu___159_14270.delta_level);
                     primitive_steps = (uu___159_14270.primitive_steps);
                     strong = (uu___159_14270.strong);
                     memoize_lazy = (uu___159_14270.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_14270.normalize_pure_lets)
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
                         let uu____14309 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14309 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_14329 = cfg  in
                               let uu____14330 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_14329.steps);
                                 tcenv = uu____14330;
                                 debug = (uu___161_14329.debug);
                                 delta_level = (uu___161_14329.delta_level);
                                 primitive_steps =
                                   (uu___161_14329.primitive_steps);
                                 strong = (uu___161_14329.strong);
                                 memoize_lazy = (uu___161_14329.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_14329.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14337 =
                                 let uu____14338 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14338  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14337
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_14341 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_14341.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_14341.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_14341.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_14341.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14342 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14342
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14353,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14354;
                               FStar_Syntax_Syntax.lbunivs = uu____14355;
                               FStar_Syntax_Syntax.lbtyp = uu____14356;
                               FStar_Syntax_Syntax.lbeff = uu____14357;
                               FStar_Syntax_Syntax.lbdef = uu____14358;
                               FStar_Syntax_Syntax.lbattrs = uu____14359;
                               FStar_Syntax_Syntax.lbpos = uu____14360;_}::uu____14361),uu____14362)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14402 =
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
               if uu____14402
               then
                 let binder =
                   let uu____14404 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14404  in
                 let env1 =
                   let uu____14414 =
                     let uu____14421 =
                       let uu____14422 =
                         let uu____14453 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14453,
                           false)
                          in
                       Clos uu____14422  in
                     ((FStar_Pervasives_Native.Some binder), uu____14421)  in
                   uu____14414 :: env  in
                 (log cfg
                    (fun uu____14546  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14550  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14551 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14551))
                 else
                   (let uu____14553 =
                      let uu____14558 =
                        let uu____14559 =
                          let uu____14560 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14560
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14559]  in
                      FStar_Syntax_Subst.open_term uu____14558 body  in
                    match uu____14553 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14569  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14577 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14577  in
                            FStar_Util.Inl
                              (let uu___163_14587 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_14587.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_14587.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14590  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_14592 = lb  in
                             let uu____14593 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_14592.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_14592.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14593;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_14592.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_14592.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14628  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_14651 = cfg  in
                             {
                               steps = (uu___165_14651.steps);
                               tcenv = (uu___165_14651.tcenv);
                               debug = (uu___165_14651.debug);
                               delta_level = (uu___165_14651.delta_level);
                               primitive_steps =
                                 (uu___165_14651.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_14651.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_14651.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14654  ->
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
               let uu____14671 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14671 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14707 =
                               let uu___166_14708 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_14708.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_14708.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14707  in
                           let uu____14709 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14709 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14735 =
                                   FStar_List.map (fun uu____14751  -> dummy)
                                     lbs1
                                    in
                                 let uu____14752 =
                                   let uu____14761 =
                                     FStar_List.map
                                       (fun uu____14781  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14761 env  in
                                 FStar_List.append uu____14735 uu____14752
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14805 =
                                       let uu___167_14806 = rc  in
                                       let uu____14807 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_14806.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14807;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_14806.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14805
                                 | uu____14814 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_14818 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_14818.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_14818.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_14818.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_14818.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14828 =
                        FStar_List.map (fun uu____14844  -> dummy) lbs2  in
                      FStar_List.append uu____14828 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14852 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14852 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_14868 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_14868.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_14868.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____14895 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14895
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14914 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14990  ->
                        match uu____14990 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_15111 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_15111.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_15111.FStar_Syntax_Syntax.sort)
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
               (match uu____14914 with
                | (rec_env,memos,uu____15324) ->
                    let uu____15377 =
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
                             let uu____15700 =
                               let uu____15707 =
                                 let uu____15708 =
                                   let uu____15739 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15739, false)
                                    in
                                 Clos uu____15708  in
                               (FStar_Pervasives_Native.None, uu____15707)
                                in
                             uu____15700 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15849  ->
                     let uu____15850 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15850);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15872 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15874::uu____15875 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15880) ->
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
                             | uu____15903 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15917 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15917
                              | uu____15928 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15932 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15958 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15976 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____15993 =
                        let uu____15994 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____15995 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15994 uu____15995
                         in
                      failwith uu____15993
                    else rebuild cfg env stack t2
                | uu____15997 -> norm cfg env stack t2))

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
                let uu____16007 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16007  in
              let uu____16008 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16008 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16021  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16032  ->
                        let uu____16033 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16034 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16033 uu____16034);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16039 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16039 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16048))::stack1 ->
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
                      | uu____16103 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16106 ->
                          let uu____16109 =
                            let uu____16110 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16110
                             in
                          failwith uu____16109
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
                  let uu___171_16134 = cfg  in
                  let uu____16135 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16135;
                    tcenv = (uu___171_16134.tcenv);
                    debug = (uu___171_16134.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_16134.primitive_steps);
                    strong = (uu___171_16134.strong);
                    memoize_lazy = (uu___171_16134.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_16134.normalize_pure_lets)
                  }
                else
                  (let uu___172_16137 = cfg  in
                   {
                     steps =
                       (let uu___173_16140 = cfg.steps  in
                        {
                          beta = (uu___173_16140.beta);
                          iota = (uu___173_16140.iota);
                          zeta = false;
                          weak = (uu___173_16140.weak);
                          hnf = (uu___173_16140.hnf);
                          primops = (uu___173_16140.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_16140.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_16140.unfold_until);
                          unfold_only = (uu___173_16140.unfold_only);
                          unfold_fully = (uu___173_16140.unfold_fully);
                          unfold_attr = (uu___173_16140.unfold_attr);
                          unfold_tac = (uu___173_16140.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_16140.pure_subterms_within_computations);
                          simplify = (uu___173_16140.simplify);
                          erase_universes = (uu___173_16140.erase_universes);
                          allow_unbound_universes =
                            (uu___173_16140.allow_unbound_universes);
                          reify_ = (uu___173_16140.reify_);
                          compress_uvars = (uu___173_16140.compress_uvars);
                          no_full_norm = (uu___173_16140.no_full_norm);
                          check_no_uvars = (uu___173_16140.check_no_uvars);
                          unmeta = (uu___173_16140.unmeta);
                          unascribe = (uu___173_16140.unascribe);
                          in_full_norm_request =
                            (uu___173_16140.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___173_16140.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___172_16137.tcenv);
                     debug = (uu___172_16137.debug);
                     delta_level = (uu___172_16137.delta_level);
                     primitive_steps = (uu___172_16137.primitive_steps);
                     strong = (uu___172_16137.strong);
                     memoize_lazy = (uu___172_16137.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_16137.normalize_pure_lets)
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
                log cfg
                  (fun uu____16170  ->
                     let uu____16171 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16172 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16171
                       uu____16172);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16174 =
                   let uu____16175 = FStar_Syntax_Subst.compress head3  in
                   uu____16175.FStar_Syntax_Syntax.n  in
                 match uu____16174 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16193 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16193
                        in
                     let uu____16194 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16194 with
                      | (uu____16195,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16201 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16211 =
                                   let uu____16212 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16212.FStar_Syntax_Syntax.n  in
                                 match uu____16211 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16218,uu____16219))
                                     ->
                                     let uu____16228 =
                                       let uu____16229 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16229.FStar_Syntax_Syntax.n  in
                                     (match uu____16228 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16235,msrc,uu____16237))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16246 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16246
                                      | uu____16247 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16248 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16249 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16249 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_16254 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_16254.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_16254.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_16254.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_16254.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_16254.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16255 = FStar_List.tl stack  in
                                    let uu____16256 =
                                      let uu____16257 =
                                        let uu____16264 =
                                          let uu____16265 =
                                            let uu____16278 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16278)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16265
                                           in
                                        FStar_Syntax_Syntax.mk uu____16264
                                         in
                                      uu____16257
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16255 uu____16256
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16294 =
                                      let uu____16295 = is_return body  in
                                      match uu____16295 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16299;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16300;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16305 -> false  in
                                    if uu____16294
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
                                         let uu____16328 =
                                           let uu____16335 =
                                             let uu____16336 =
                                               let uu____16353 =
                                                 let uu____16356 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16356]  in
                                               (uu____16353, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16336
                                              in
                                           FStar_Syntax_Syntax.mk uu____16335
                                            in
                                         uu____16328
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16374 =
                                           let uu____16375 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16375.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16374 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16381::uu____16382::[])
                                             ->
                                             let uu____16389 =
                                               let uu____16396 =
                                                 let uu____16397 =
                                                   let uu____16404 =
                                                     let uu____16407 =
                                                       let uu____16408 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16408
                                                        in
                                                     let uu____16409 =
                                                       let uu____16412 =
                                                         let uu____16413 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16413
                                                          in
                                                       [uu____16412]  in
                                                     uu____16407 ::
                                                       uu____16409
                                                      in
                                                   (bind1, uu____16404)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16397
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16396
                                                in
                                             uu____16389
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16421 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16427 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16427
                                         then
                                           let uu____16430 =
                                             let uu____16431 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16431
                                              in
                                           let uu____16432 =
                                             let uu____16435 =
                                               let uu____16436 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16436
                                                in
                                             [uu____16435]  in
                                           uu____16430 :: uu____16432
                                         else []  in
                                       let reified =
                                         let uu____16441 =
                                           let uu____16448 =
                                             let uu____16449 =
                                               let uu____16464 =
                                                 let uu____16467 =
                                                   let uu____16470 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16471 =
                                                     let uu____16474 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16474]  in
                                                   uu____16470 :: uu____16471
                                                    in
                                                 let uu____16475 =
                                                   let uu____16478 =
                                                     let uu____16481 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16482 =
                                                       let uu____16485 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16486 =
                                                         let uu____16489 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16490 =
                                                           let uu____16493 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16493]  in
                                                         uu____16489 ::
                                                           uu____16490
                                                          in
                                                       uu____16485 ::
                                                         uu____16486
                                                        in
                                                     uu____16481 ::
                                                       uu____16482
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16478
                                                    in
                                                 FStar_List.append
                                                   uu____16467 uu____16475
                                                  in
                                               (bind_inst, uu____16464)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16449
                                              in
                                           FStar_Syntax_Syntax.mk uu____16448
                                            in
                                         uu____16441
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16505  ->
                                            let uu____16506 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16507 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16506 uu____16507);
                                       (let uu____16508 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16508 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16532 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16532
                        in
                     let uu____16533 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16533 with
                      | (uu____16534,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16573 =
                                  let uu____16574 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16574.FStar_Syntax_Syntax.n  in
                                match uu____16573 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16580) -> t2
                                | uu____16585 -> head4  in
                              let uu____16586 =
                                let uu____16587 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16587.FStar_Syntax_Syntax.n  in
                              match uu____16586 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16593 -> FStar_Pervasives_Native.None
                               in
                            let uu____16594 = maybe_extract_fv head4  in
                            match uu____16594 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16604 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16604
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16609 = maybe_extract_fv head5
                                     in
                                  match uu____16609 with
                                  | FStar_Pervasives_Native.Some uu____16614
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16615 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16620 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16637 =
                              match uu____16637 with
                              | (e,q) ->
                                  let uu____16644 =
                                    let uu____16645 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16645.FStar_Syntax_Syntax.n  in
                                  (match uu____16644 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16660 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16660
                                   | uu____16661 -> false)
                               in
                            let uu____16662 =
                              let uu____16663 =
                                let uu____16670 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16670 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16663
                               in
                            if uu____16662
                            then
                              let uu____16675 =
                                let uu____16676 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16676
                                 in
                              failwith uu____16675
                            else ());
                           (let uu____16678 = maybe_unfold_action head_app
                               in
                            match uu____16678 with
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
                                   (fun uu____16721  ->
                                      let uu____16722 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16723 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16722 uu____16723);
                                 (let uu____16724 = FStar_List.tl stack  in
                                  norm cfg env uu____16724 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16726) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16750 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16750  in
                     (log cfg
                        (fun uu____16754  ->
                           let uu____16755 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16755);
                      (let uu____16756 = FStar_List.tl stack  in
                       norm cfg env uu____16756 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16877  ->
                               match uu____16877 with
                               | (pat,wopt,tm) ->
                                   let uu____16925 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____16925)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____16957 = FStar_List.tl stack  in
                     norm cfg env uu____16957 tm
                 | uu____16958 -> fallback ())

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
              (fun uu____16972  ->
                 let uu____16973 = FStar_Ident.string_of_lid msrc  in
                 let uu____16974 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16975 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16973
                   uu____16974 uu____16975);
            (let uu____16976 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16976
             then
               let ed =
                 let uu____16978 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16978  in
               let uu____16979 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16979 with
               | (uu____16980,return_repr) ->
                   let return_inst =
                     let uu____16989 =
                       let uu____16990 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16990.FStar_Syntax_Syntax.n  in
                     match uu____16989 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16996::[]) ->
                         let uu____17003 =
                           let uu____17010 =
                             let uu____17011 =
                               let uu____17018 =
                                 let uu____17021 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17021]  in
                               (return_tm, uu____17018)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17011  in
                           FStar_Syntax_Syntax.mk uu____17010  in
                         uu____17003 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17029 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17032 =
                     let uu____17039 =
                       let uu____17040 =
                         let uu____17055 =
                           let uu____17058 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17059 =
                             let uu____17062 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17062]  in
                           uu____17058 :: uu____17059  in
                         (return_inst, uu____17055)  in
                       FStar_Syntax_Syntax.Tm_app uu____17040  in
                     FStar_Syntax_Syntax.mk uu____17039  in
                   uu____17032 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17071 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17071 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17074 =
                      let uu____17075 = FStar_Ident.text_of_lid msrc  in
                      let uu____17076 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17075 uu____17076
                       in
                    failwith uu____17074
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17077;
                      FStar_TypeChecker_Env.mtarget = uu____17078;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17079;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17101 =
                      let uu____17102 = FStar_Ident.text_of_lid msrc  in
                      let uu____17103 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17102 uu____17103
                       in
                    failwith uu____17101
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17104;
                      FStar_TypeChecker_Env.mtarget = uu____17105;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17106;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17141 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17142 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17141 t FStar_Syntax_Syntax.tun uu____17142))

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
                (fun uu____17198  ->
                   match uu____17198 with
                   | (a,imp) ->
                       let uu____17209 = norm cfg env [] a  in
                       (uu____17209, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17217  ->
             let uu____17218 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17219 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17218 uu____17219);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17243 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17243
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_17246 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_17246.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_17246.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17266 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____17266
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_17269 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_17269.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_17269.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17304  ->
                      match uu____17304 with
                      | (a,i) ->
                          let uu____17315 = norm cfg env [] a  in
                          (uu____17315, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_17333  ->
                       match uu___90_17333 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17337 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17337
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_17345 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_17348 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_17348.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_17345.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_17345.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17351  ->
        match uu____17351 with
        | (x,imp) ->
            let uu____17354 =
              let uu___179_17355 = x  in
              let uu____17356 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_17355.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_17355.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17356
              }  in
            (uu____17354, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17362 =
          FStar_List.fold_left
            (fun uu____17380  ->
               fun b  ->
                 match uu____17380 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17362 with | (nbs,uu____17420) -> FStar_List.rev nbs

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
            let uu____17436 =
              let uu___180_17437 = rc  in
              let uu____17438 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_17437.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17438;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_17437.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17436
        | uu____17445 -> lopt

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
            (let uu____17466 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17467 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17466
               uu____17467)
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
          let uu____17487 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17487
          then tm1
          else
            (let w t =
               let uu___181_17501 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_17501.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_17501.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17512 =
                 let uu____17513 = FStar_Syntax_Util.unmeta t  in
                 uu____17513.FStar_Syntax_Syntax.n  in
               match uu____17512 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17520 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17569)::args1,(bv,uu____17572)::bs1) ->
                   let uu____17606 =
                     let uu____17607 = FStar_Syntax_Subst.compress t  in
                     uu____17607.FStar_Syntax_Syntax.n  in
                   (match uu____17606 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17611 -> false)
               | ([],[]) -> true
               | (uu____17632,uu____17633) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17674 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17675 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17674
                    uu____17675)
               else ();
               (let uu____17677 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17677 with
                | (hd1,args) ->
                    let uu____17710 =
                      let uu____17711 = FStar_Syntax_Subst.compress hd1  in
                      uu____17711.FStar_Syntax_Syntax.n  in
                    (match uu____17710 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____17718 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17719 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17720 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17718 uu____17719 uu____17720)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17722 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17739 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17740 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17739
                    uu____17740)
               else ();
               (let uu____17742 = FStar_Syntax_Util.is_squash t  in
                match uu____17742 with
                | FStar_Pervasives_Native.Some (uu____17753,t') ->
                    is_applied bs t'
                | uu____17765 ->
                    let uu____17774 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17774 with
                     | FStar_Pervasives_Native.Some (uu____17785,t') ->
                         is_applied bs t'
                     | uu____17797 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17821 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17821 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17828)::(q,uu____17830)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____17866 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17867 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17866 uu____17867)
                    else ();
                    (let uu____17869 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17869 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17874 =
                           let uu____17875 = FStar_Syntax_Subst.compress p
                              in
                           uu____17875.FStar_Syntax_Syntax.n  in
                         (match uu____17874 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17883 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17883))
                          | uu____17884 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17887)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17912 =
                           let uu____17913 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17913.FStar_Syntax_Syntax.n  in
                         (match uu____17912 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17921 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17921))
                          | uu____17922 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17926 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17926 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17931 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17931 with
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
                                     let uu____17940 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17940))
                               | uu____17941 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17946)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17971 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17971 with
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
                                     let uu____17980 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17980))
                               | uu____17981 -> FStar_Pervasives_Native.None)
                          | uu____17984 -> FStar_Pervasives_Native.None)
                     | uu____17987 -> FStar_Pervasives_Native.None))
               | uu____17990 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18003 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18003 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18009)::[],uu____18010,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18027 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18028 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18027
                         uu____18028)
                    else ();
                    is_quantified_const bv phi')
               | uu____18030 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18043 =
                 let uu____18044 = FStar_Syntax_Subst.compress phi  in
                 uu____18044.FStar_Syntax_Syntax.n  in
               match uu____18043 with
               | FStar_Syntax_Syntax.Tm_match (uu____18049,br::brs) ->
                   let uu____18116 = br  in
                   (match uu____18116 with
                    | (uu____18133,uu____18134,e) ->
                        let r =
                          let uu____18155 = simp_t e  in
                          match uu____18155 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18161 =
                                FStar_List.for_all
                                  (fun uu____18179  ->
                                     match uu____18179 with
                                     | (uu____18192,uu____18193,e') ->
                                         let uu____18207 = simp_t e'  in
                                         uu____18207 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18161
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18215 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18222 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18222
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18247 =
                 match uu____18247 with
                 | (t1,q) ->
                     let uu____18260 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18260 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18288 -> (t1, q))
                  in
               let uu____18297 = FStar_Syntax_Util.head_and_args t  in
               match uu____18297 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18361 =
                 let uu____18362 = FStar_Syntax_Util.unmeta ty  in
                 uu____18362.FStar_Syntax_Syntax.n  in
               match uu____18361 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18366) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18371,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18391 -> false  in
             let simplify1 arg =
               let uu____18416 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18416, arg)  in
             let uu____18425 = is_forall_const tm1  in
             match uu____18425 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____18430 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18431 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18430
                       uu____18431)
                  else ();
                  (let uu____18433 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18433))
             | FStar_Pervasives_Native.None  ->
                 let uu____18434 =
                   let uu____18435 = FStar_Syntax_Subst.compress tm1  in
                   uu____18435.FStar_Syntax_Syntax.n  in
                 (match uu____18434 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18439;
                              FStar_Syntax_Syntax.vars = uu____18440;_},uu____18441);
                         FStar_Syntax_Syntax.pos = uu____18442;
                         FStar_Syntax_Syntax.vars = uu____18443;_},args)
                      ->
                      let uu____18469 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18469
                      then
                        let uu____18470 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18470 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18517)::
                             (uu____18518,(arg,uu____18520))::[] ->
                             maybe_auto_squash arg
                         | (uu____18569,(arg,uu____18571))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18572)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18621)::uu____18622::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18673::(FStar_Pervasives_Native.Some (false
                                         ),uu____18674)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18725 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18739 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18739
                         then
                           let uu____18740 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18740 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18787)::uu____18788::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18839::(FStar_Pervasives_Native.Some (true
                                           ),uu____18840)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18891)::(uu____18892,(arg,uu____18894))::[]
                               -> maybe_auto_squash arg
                           | (uu____18943,(arg,uu____18945))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18946)::[]
                               -> maybe_auto_squash arg
                           | uu____18995 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19009 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19009
                            then
                              let uu____19010 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19010 with
                              | uu____19057::(FStar_Pervasives_Native.Some
                                              (true ),uu____19058)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19109)::uu____19110::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19161)::(uu____19162,(arg,uu____19164))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19213,(p,uu____19215))::(uu____19216,
                                                                (q,uu____19218))::[]
                                  ->
                                  let uu____19265 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19265
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19267 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19281 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19281
                               then
                                 let uu____19282 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19282 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19329)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19330)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19381)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19382)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19433)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19434)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19485)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19486)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19537,(arg,uu____19539))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19540)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19589)::(uu____19590,(arg,uu____19592))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19641,(arg,uu____19643))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19644)::[]
                                     ->
                                     let uu____19693 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19693
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19694)::(uu____19695,(arg,uu____19697))::[]
                                     ->
                                     let uu____19746 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19746
                                 | (uu____19747,(p,uu____19749))::(uu____19750,
                                                                   (q,uu____19752))::[]
                                     ->
                                     let uu____19799 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19799
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19801 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19815 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19815
                                  then
                                    let uu____19816 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19816 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19863)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19894)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19925 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19939 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19939
                                     then
                                       match args with
                                       | (t,uu____19941)::[] ->
                                           let uu____19958 =
                                             let uu____19959 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19959.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19958 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19962::[],body,uu____19964)
                                                ->
                                                let uu____19991 = simp_t body
                                                   in
                                                (match uu____19991 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19994 -> tm1)
                                            | uu____19997 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19999))::(t,uu____20001)::[]
                                           ->
                                           let uu____20040 =
                                             let uu____20041 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20041.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20040 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20044::[],body,uu____20046)
                                                ->
                                                let uu____20073 = simp_t body
                                                   in
                                                (match uu____20073 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20076 -> tm1)
                                            | uu____20079 -> tm1)
                                       | uu____20080 -> tm1
                                     else
                                       (let uu____20090 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20090
                                        then
                                          match args with
                                          | (t,uu____20092)::[] ->
                                              let uu____20109 =
                                                let uu____20110 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20110.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20109 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20113::[],body,uu____20115)
                                                   ->
                                                   let uu____20142 =
                                                     simp_t body  in
                                                   (match uu____20142 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20145 -> tm1)
                                               | uu____20148 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20150))::(t,uu____20152)::[]
                                              ->
                                              let uu____20191 =
                                                let uu____20192 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20192.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20191 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20195::[],body,uu____20197)
                                                   ->
                                                   let uu____20224 =
                                                     simp_t body  in
                                                   (match uu____20224 with
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
                                                    | uu____20227 -> tm1)
                                               | uu____20230 -> tm1)
                                          | uu____20231 -> tm1
                                        else
                                          (let uu____20241 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20241
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20242;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20243;_},uu____20244)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20261;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20262;_},uu____20263)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20280 -> tm1
                                           else
                                             (let uu____20290 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20290 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20310 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20320;
                         FStar_Syntax_Syntax.vars = uu____20321;_},args)
                      ->
                      let uu____20343 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20343
                      then
                        let uu____20344 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20344 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20391)::
                             (uu____20392,(arg,uu____20394))::[] ->
                             maybe_auto_squash arg
                         | (uu____20443,(arg,uu____20445))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20446)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20495)::uu____20496::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20547::(FStar_Pervasives_Native.Some (false
                                         ),uu____20548)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20599 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20613 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20613
                         then
                           let uu____20614 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20614 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20661)::uu____20662::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20713::(FStar_Pervasives_Native.Some (true
                                           ),uu____20714)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20765)::(uu____20766,(arg,uu____20768))::[]
                               -> maybe_auto_squash arg
                           | (uu____20817,(arg,uu____20819))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20820)::[]
                               -> maybe_auto_squash arg
                           | uu____20869 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20883 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20883
                            then
                              let uu____20884 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20884 with
                              | uu____20931::(FStar_Pervasives_Native.Some
                                              (true ),uu____20932)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20983)::uu____20984::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21035)::(uu____21036,(arg,uu____21038))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21087,(p,uu____21089))::(uu____21090,
                                                                (q,uu____21092))::[]
                                  ->
                                  let uu____21139 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21139
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21141 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21155 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21155
                               then
                                 let uu____21156 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21156 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21203)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21204)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21255)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21256)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21307)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21308)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21359)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21360)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21411,(arg,uu____21413))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21414)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21463)::(uu____21464,(arg,uu____21466))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21515,(arg,uu____21517))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21518)::[]
                                     ->
                                     let uu____21567 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21567
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21568)::(uu____21569,(arg,uu____21571))::[]
                                     ->
                                     let uu____21620 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21620
                                 | (uu____21621,(p,uu____21623))::(uu____21624,
                                                                   (q,uu____21626))::[]
                                     ->
                                     let uu____21673 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21673
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21675 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21689 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21689
                                  then
                                    let uu____21690 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21690 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21737)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21768)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21799 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21813 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21813
                                     then
                                       match args with
                                       | (t,uu____21815)::[] ->
                                           let uu____21832 =
                                             let uu____21833 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21833.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21832 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21836::[],body,uu____21838)
                                                ->
                                                let uu____21865 = simp_t body
                                                   in
                                                (match uu____21865 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21868 -> tm1)
                                            | uu____21871 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21873))::(t,uu____21875)::[]
                                           ->
                                           let uu____21914 =
                                             let uu____21915 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21915.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21914 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21918::[],body,uu____21920)
                                                ->
                                                let uu____21947 = simp_t body
                                                   in
                                                (match uu____21947 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21950 -> tm1)
                                            | uu____21953 -> tm1)
                                       | uu____21954 -> tm1
                                     else
                                       (let uu____21964 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21964
                                        then
                                          match args with
                                          | (t,uu____21966)::[] ->
                                              let uu____21983 =
                                                let uu____21984 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21984.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21983 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21987::[],body,uu____21989)
                                                   ->
                                                   let uu____22016 =
                                                     simp_t body  in
                                                   (match uu____22016 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22019 -> tm1)
                                               | uu____22022 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22024))::(t,uu____22026)::[]
                                              ->
                                              let uu____22065 =
                                                let uu____22066 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22066.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22065 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22069::[],body,uu____22071)
                                                   ->
                                                   let uu____22098 =
                                                     simp_t body  in
                                                   (match uu____22098 with
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
                                                    | uu____22101 -> tm1)
                                               | uu____22104 -> tm1)
                                          | uu____22105 -> tm1
                                        else
                                          (let uu____22115 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22115
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22116;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22117;_},uu____22118)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22135;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22136;_},uu____22137)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22154 -> tm1
                                           else
                                             (let uu____22164 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22164 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22184 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22199 = simp_t t  in
                      (match uu____22199 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22202 ->
                      let uu____22225 = is_const_match tm1  in
                      (match uu____22225 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22228 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22238  ->
               (let uu____22240 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22241 = FStar_Syntax_Print.term_to_string t  in
                let uu____22242 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22249 =
                  let uu____22250 =
                    let uu____22253 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22253
                     in
                  stack_to_string uu____22250  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22240 uu____22241 uu____22242 uu____22249);
               (let uu____22276 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22276
                then
                  let uu____22277 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22277 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22284 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22285 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22286 =
                          let uu____22287 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22287
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22284
                          uu____22285 uu____22286);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22305 =
                     let uu____22306 =
                       let uu____22307 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22307  in
                     FStar_Util.string_of_int uu____22306  in
                   let uu____22312 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22313 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22305 uu____22312 uu____22313)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22319,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22368  ->
                     let uu____22369 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22369);
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
               let uu____22405 =
                 let uu___182_22406 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_22406.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_22406.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22405
           | (Arg (Univ uu____22407,uu____22408,uu____22409))::uu____22410 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22413,uu____22414))::uu____22415 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22430,uu____22431),aq,r))::stack1
               when
               let uu____22481 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22481 ->
               let t2 =
                 let uu____22485 =
                   let uu____22490 =
                     let uu____22491 = closure_as_term cfg env_arg tm  in
                     (uu____22491, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22490  in
                 uu____22485 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22497),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22550  ->
                     let uu____22551 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22551);
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
                  (let uu____22561 = FStar_ST.op_Bang m  in
                   match uu____22561 with
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
                   | FStar_Pervasives_Native.Some (uu____22702,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22753 =
                 log cfg
                   (fun uu____22757  ->
                      let uu____22758 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22758);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22762 =
                 let uu____22763 = FStar_Syntax_Subst.compress t1  in
                 uu____22763.FStar_Syntax_Syntax.n  in
               (match uu____22762 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22790 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22790  in
                    (log cfg
                       (fun uu____22794  ->
                          let uu____22795 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22795);
                     (let uu____22796 = FStar_List.tl stack  in
                      norm cfg env1 uu____22796 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22797);
                       FStar_Syntax_Syntax.pos = uu____22798;
                       FStar_Syntax_Syntax.vars = uu____22799;_},(e,uu____22801)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22830 when
                    (cfg.steps).primops ->
                    let uu____22845 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22845 with
                     | (hd1,args) ->
                         let uu____22882 =
                           let uu____22883 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____22883.FStar_Syntax_Syntax.n  in
                         (match uu____22882 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____22887 = find_prim_step cfg fv  in
                              (match uu____22887 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____22890; arity = uu____22891;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____22893;
                                     requires_binder_substitution =
                                       uu____22894;
                                     interpretation = uu____22895;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____22910 -> fallback " (3)" ())
                          | uu____22913 -> fallback " (4)" ()))
                | uu____22914 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____22935  ->
                     let uu____22936 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22936);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____22945 =
                   log cfg1
                     (fun uu____22950  ->
                        let uu____22951 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____22952 =
                          let uu____22953 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____22970  ->
                                    match uu____22970 with
                                    | (p,uu____22980,uu____22981) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____22953
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____22951 uu____22952);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_22998  ->
                                match uu___91_22998 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____22999 -> false))
                         in
                      let steps =
                        let uu___183_23001 = cfg1.steps  in
                        {
                          beta = (uu___183_23001.beta);
                          iota = (uu___183_23001.iota);
                          zeta = false;
                          weak = (uu___183_23001.weak);
                          hnf = (uu___183_23001.hnf);
                          primops = (uu___183_23001.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_23001.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_23001.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_23001.pure_subterms_within_computations);
                          simplify = (uu___183_23001.simplify);
                          erase_universes = (uu___183_23001.erase_universes);
                          allow_unbound_universes =
                            (uu___183_23001.allow_unbound_universes);
                          reify_ = (uu___183_23001.reify_);
                          compress_uvars = (uu___183_23001.compress_uvars);
                          no_full_norm = (uu___183_23001.no_full_norm);
                          check_no_uvars = (uu___183_23001.check_no_uvars);
                          unmeta = (uu___183_23001.unmeta);
                          unascribe = (uu___183_23001.unascribe);
                          in_full_norm_request =
                            (uu___183_23001.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___183_23001.weakly_reduce_scrutinee)
                        }  in
                      let uu___184_23006 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_23006.tcenv);
                        debug = (uu___184_23006.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_23006.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_23006.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_23006.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23046 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23067 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23127  ->
                                    fun uu____23128  ->
                                      match (uu____23127, uu____23128) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23219 = norm_pat env3 p1
                                             in
                                          (match uu____23219 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23067 with
                           | (pats1,env3) ->
                               ((let uu___185_23301 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_23301.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_23320 = x  in
                            let uu____23321 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_23320.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_23320.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23321
                            }  in
                          ((let uu___187_23335 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_23335.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_23346 = x  in
                            let uu____23347 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_23346.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_23346.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23347
                            }  in
                          ((let uu___189_23361 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_23361.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_23377 = x  in
                            let uu____23378 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_23377.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_23377.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23378
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_23385 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_23385.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23395 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23409 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23409 with
                                  | (p,wopt,e) ->
                                      let uu____23429 = norm_pat env1 p  in
                                      (match uu____23429 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23454 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23454
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23461 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23461
                      then
                        norm
                          (let uu___192_23464 = cfg1  in
                           {
                             steps =
                               (let uu___193_23467 = cfg1.steps  in
                                {
                                  beta = (uu___193_23467.beta);
                                  iota = (uu___193_23467.iota);
                                  zeta = (uu___193_23467.zeta);
                                  weak = (uu___193_23467.weak);
                                  hnf = (uu___193_23467.hnf);
                                  primops = (uu___193_23467.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___193_23467.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___193_23467.unfold_until);
                                  unfold_only = (uu___193_23467.unfold_only);
                                  unfold_fully =
                                    (uu___193_23467.unfold_fully);
                                  unfold_attr = (uu___193_23467.unfold_attr);
                                  unfold_tac = (uu___193_23467.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___193_23467.pure_subterms_within_computations);
                                  simplify = (uu___193_23467.simplify);
                                  erase_universes =
                                    (uu___193_23467.erase_universes);
                                  allow_unbound_universes =
                                    (uu___193_23467.allow_unbound_universes);
                                  reify_ = (uu___193_23467.reify_);
                                  compress_uvars =
                                    (uu___193_23467.compress_uvars);
                                  no_full_norm =
                                    (uu___193_23467.no_full_norm);
                                  check_no_uvars =
                                    (uu___193_23467.check_no_uvars);
                                  unmeta = (uu___193_23467.unmeta);
                                  unascribe = (uu___193_23467.unascribe);
                                  in_full_norm_request =
                                    (uu___193_23467.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___192_23464.tcenv);
                             debug = (uu___192_23464.debug);
                             delta_level = (uu___192_23464.delta_level);
                             primitive_steps =
                               (uu___192_23464.primitive_steps);
                             strong = (uu___192_23464.strong);
                             memoize_lazy = (uu___192_23464.memoize_lazy);
                             normalize_pure_lets =
                               (uu___192_23464.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23469 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23469)
                    in
                 let rec is_cons head1 =
                   let uu____23476 =
                     let uu____23477 = FStar_Syntax_Subst.compress head1  in
                     uu____23477.FStar_Syntax_Syntax.n  in
                   match uu____23476 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23481) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23486 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23487;
                         FStar_Syntax_Syntax.fv_delta = uu____23488;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23489;
                         FStar_Syntax_Syntax.fv_delta = uu____23490;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23491);_}
                       -> true
                   | uu____23498 -> false  in
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
                   let uu____23659 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23659 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23746 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23785 ->
                                 let uu____23786 =
                                   let uu____23787 = is_cons head1  in
                                   Prims.op_Negation uu____23787  in
                                 FStar_Util.Inr uu____23786)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23812 =
                              let uu____23813 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23813.FStar_Syntax_Syntax.n  in
                            (match uu____23812 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23831 ->
                                 let uu____23832 =
                                   let uu____23833 = is_cons head1  in
                                   Prims.op_Negation uu____23833  in
                                 FStar_Util.Inr uu____23832))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____23902)::rest_a,(p1,uu____23905)::rest_p) ->
                       let uu____23949 = matches_pat t2 p1  in
                       (match uu____23949 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____23998 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24108 = matches_pat scrutinee1 p1  in
                       (match uu____24108 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24148  ->
                                  let uu____24149 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24150 =
                                    let uu____24151 =
                                      FStar_List.map
                                        (fun uu____24161  ->
                                           match uu____24161 with
                                           | (uu____24166,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24151
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24149 uu____24150);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24198  ->
                                       match uu____24198 with
                                       | (bv,t2) ->
                                           let uu____24221 =
                                             let uu____24228 =
                                               let uu____24231 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24231
                                                in
                                             let uu____24232 =
                                               let uu____24233 =
                                                 let uu____24264 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24264, false)
                                                  in
                                               Clos uu____24233  in
                                             (uu____24228, uu____24232)  in
                                           uu____24221 :: env2) env1 s
                                 in
                              let uu____24381 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24381)))
                    in
                 if (cfg1.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____24408 =
      let uu____24411 = FStar_ST.op_Bang plugins  in p :: uu____24411  in
    FStar_ST.op_Colon_Equals plugins uu____24408  in
  let retrieve uu____24519 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24596  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_24637  ->
                  match uu___92_24637 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24641 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24647 -> d  in
        let uu____24650 = to_fsteps s  in
        let uu____24651 =
          let uu____24652 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24653 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24654 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24655 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____24656 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24657 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24652;
            primop = uu____24653;
            b380 = uu____24654;
            wpe = uu____24655;
            norm_delayed = uu____24656;
            print_normalized = uu____24657
          }  in
        let uu____24658 =
          let uu____24661 = FStar_Util.smap_copy built_in_primitive_steps  in
          let uu____24664 =
            let uu____24667 = retrieve_plugins ()  in
            FStar_List.append uu____24667 psteps  in
          add_steps uu____24661 uu____24664  in
        let uu____24670 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24672 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24672)
           in
        {
          steps = uu____24650;
          tcenv = e;
          debug = uu____24651;
          delta_level = d1;
          primitive_steps = uu____24658;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24670
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
      fun t  -> let uu____24754 = config s e  in norm_comp uu____24754 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24771 = config [] env  in norm_universe uu____24771 [] u
  
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
        let uu____24795 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24795  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24802 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___194_24821 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___194_24821.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___194_24821.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24828 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24828
          then
            let ct1 =
              let uu____24830 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24830 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24837 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24837
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___195_24841 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___195_24841.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___195_24841.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___195_24841.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___196_24843 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___196_24843.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___196_24843.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___196_24843.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___196_24843.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___197_24844 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___197_24844.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_24844.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24846 -> c
  
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
        let uu____24864 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24864  in
      let uu____24871 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24871
      then
        let uu____24872 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24872 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24878  ->
                 let uu____24879 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24879)
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
            ((let uu____24900 =
                let uu____24905 =
                  let uu____24906 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24906
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24905)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24900);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24921 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24921 [] c
        with
        | e ->
            ((let uu____24934 =
                let uu____24939 =
                  let uu____24940 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24940
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24939)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24934);
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
                   let uu____24985 =
                     let uu____24986 =
                       let uu____24993 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24993)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24986  in
                   mk uu____24985 t01.FStar_Syntax_Syntax.pos
               | uu____24998 -> t2)
          | uu____24999 -> t2  in
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
        let uu____25063 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25063 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25092 ->
                 let uu____25099 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25099 with
                  | (actuals,uu____25109,uu____25110) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25124 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25124 with
                         | (binders,args) ->
                             let uu____25141 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25141
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
      | uu____25153 ->
          let uu____25154 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25154 with
           | (head1,args) ->
               let uu____25191 =
                 let uu____25192 = FStar_Syntax_Subst.compress head1  in
                 uu____25192.FStar_Syntax_Syntax.n  in
               (match uu____25191 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25195,thead) ->
                    let uu____25221 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25221 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25263 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___202_25271 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___202_25271.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___202_25271.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___202_25271.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___202_25271.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___202_25271.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___202_25271.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___202_25271.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___202_25271.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___202_25271.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___202_25271.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___202_25271.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___202_25271.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___202_25271.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___202_25271.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___202_25271.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___202_25271.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___202_25271.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___202_25271.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___202_25271.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___202_25271.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___202_25271.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___202_25271.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___202_25271.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___202_25271.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___202_25271.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___202_25271.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___202_25271.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___202_25271.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___202_25271.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___202_25271.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___202_25271.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___202_25271.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___202_25271.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___202_25271.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25263 with
                            | (uu____25272,ty,uu____25274) ->
                                eta_expand_with_type env t ty))
                | uu____25275 ->
                    let uu____25276 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___203_25284 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___203_25284.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___203_25284.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___203_25284.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___203_25284.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___203_25284.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___203_25284.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___203_25284.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___203_25284.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___203_25284.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___203_25284.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___203_25284.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___203_25284.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___203_25284.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___203_25284.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___203_25284.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___203_25284.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___203_25284.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___203_25284.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___203_25284.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___203_25284.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___203_25284.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___203_25284.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___203_25284.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___203_25284.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___203_25284.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___203_25284.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___203_25284.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___203_25284.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___203_25284.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___203_25284.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___203_25284.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___203_25284.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___203_25284.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___203_25284.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25276 with
                     | (uu____25285,ty,uu____25287) ->
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
      let uu___204_25360 = x  in
      let uu____25361 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___204_25360.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___204_25360.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25361
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25364 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25389 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25390 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25391 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25392 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25399 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25400 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25401 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___205_25431 = rc  in
          let uu____25432 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25439 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___205_25431.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25432;
            FStar_Syntax_Syntax.residual_flags = uu____25439
          }  in
        let uu____25442 =
          let uu____25443 =
            let uu____25460 = elim_delayed_subst_binders bs  in
            let uu____25467 = elim_delayed_subst_term t2  in
            let uu____25468 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25460, uu____25467, uu____25468)  in
          FStar_Syntax_Syntax.Tm_abs uu____25443  in
        mk1 uu____25442
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25497 =
          let uu____25498 =
            let uu____25511 = elim_delayed_subst_binders bs  in
            let uu____25518 = elim_delayed_subst_comp c  in
            (uu____25511, uu____25518)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25498  in
        mk1 uu____25497
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25531 =
          let uu____25532 =
            let uu____25539 = elim_bv bv  in
            let uu____25540 = elim_delayed_subst_term phi  in
            (uu____25539, uu____25540)  in
          FStar_Syntax_Syntax.Tm_refine uu____25532  in
        mk1 uu____25531
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25563 =
          let uu____25564 =
            let uu____25579 = elim_delayed_subst_term t2  in
            let uu____25580 = elim_delayed_subst_args args  in
            (uu____25579, uu____25580)  in
          FStar_Syntax_Syntax.Tm_app uu____25564  in
        mk1 uu____25563
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___206_25646 = p  in
              let uu____25647 =
                let uu____25648 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25648  in
              {
                FStar_Syntax_Syntax.v = uu____25647;
                FStar_Syntax_Syntax.p =
                  (uu___206_25646.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___207_25650 = p  in
              let uu____25651 =
                let uu____25652 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25652  in
              {
                FStar_Syntax_Syntax.v = uu____25651;
                FStar_Syntax_Syntax.p =
                  (uu___207_25650.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___208_25659 = p  in
              let uu____25660 =
                let uu____25661 =
                  let uu____25668 = elim_bv x  in
                  let uu____25669 = elim_delayed_subst_term t0  in
                  (uu____25668, uu____25669)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25661  in
              {
                FStar_Syntax_Syntax.v = uu____25660;
                FStar_Syntax_Syntax.p =
                  (uu___208_25659.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___209_25688 = p  in
              let uu____25689 =
                let uu____25690 =
                  let uu____25703 =
                    FStar_List.map
                      (fun uu____25726  ->
                         match uu____25726 with
                         | (x,b) ->
                             let uu____25739 = elim_pat x  in
                             (uu____25739, b)) pats
                     in
                  (fv, uu____25703)  in
                FStar_Syntax_Syntax.Pat_cons uu____25690  in
              {
                FStar_Syntax_Syntax.v = uu____25689;
                FStar_Syntax_Syntax.p =
                  (uu___209_25688.FStar_Syntax_Syntax.p)
              }
          | uu____25752 -> p  in
        let elim_branch uu____25776 =
          match uu____25776 with
          | (pat,wopt,t3) ->
              let uu____25802 = elim_pat pat  in
              let uu____25805 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25808 = elim_delayed_subst_term t3  in
              (uu____25802, uu____25805, uu____25808)
           in
        let uu____25813 =
          let uu____25814 =
            let uu____25837 = elim_delayed_subst_term t2  in
            let uu____25838 = FStar_List.map elim_branch branches  in
            (uu____25837, uu____25838)  in
          FStar_Syntax_Syntax.Tm_match uu____25814  in
        mk1 uu____25813
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25949 =
          match uu____25949 with
          | (tc,topt) ->
              let uu____25984 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25994 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25994
                | FStar_Util.Inr c ->
                    let uu____25996 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25996
                 in
              let uu____25997 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25984, uu____25997)
           in
        let uu____26006 =
          let uu____26007 =
            let uu____26034 = elim_delayed_subst_term t2  in
            let uu____26035 = elim_ascription a  in
            (uu____26034, uu____26035, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26007  in
        mk1 uu____26006
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___210_26082 = lb  in
          let uu____26083 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26086 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___210_26082.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___210_26082.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26083;
            FStar_Syntax_Syntax.lbeff =
              (uu___210_26082.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26086;
            FStar_Syntax_Syntax.lbattrs =
              (uu___210_26082.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___210_26082.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26089 =
          let uu____26090 =
            let uu____26103 =
              let uu____26110 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26110)  in
            let uu____26119 = elim_delayed_subst_term t2  in
            (uu____26103, uu____26119)  in
          FStar_Syntax_Syntax.Tm_let uu____26090  in
        mk1 uu____26089
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26152 =
          let uu____26153 =
            let uu____26170 = elim_delayed_subst_term t2  in
            (uv, uu____26170)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26153  in
        mk1 uu____26152
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26188 =
          let uu____26189 =
            let uu____26196 = elim_delayed_subst_term tm  in
            (uu____26196, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26189  in
        mk1 uu____26188
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26203 =
          let uu____26204 =
            let uu____26211 = elim_delayed_subst_term t2  in
            let uu____26212 = elim_delayed_subst_meta md  in
            (uu____26211, uu____26212)  in
          FStar_Syntax_Syntax.Tm_meta uu____26204  in
        mk1 uu____26203

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_26219  ->
         match uu___93_26219 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26223 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26223
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
        let uu____26246 =
          let uu____26247 =
            let uu____26256 = elim_delayed_subst_term t  in
            (uu____26256, uopt)  in
          FStar_Syntax_Syntax.Total uu____26247  in
        mk1 uu____26246
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26269 =
          let uu____26270 =
            let uu____26279 = elim_delayed_subst_term t  in
            (uu____26279, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26270  in
        mk1 uu____26269
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___211_26284 = ct  in
          let uu____26285 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26288 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26297 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___211_26284.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___211_26284.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26285;
            FStar_Syntax_Syntax.effect_args = uu____26288;
            FStar_Syntax_Syntax.flags = uu____26297
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_26300  ->
    match uu___94_26300 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26312 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26312
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26345 =
          let uu____26352 = elim_delayed_subst_term t  in (m, uu____26352)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26345
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26360 =
          let uu____26369 = elim_delayed_subst_term t  in
          (m1, m2, uu____26369)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26360
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26392  ->
         match uu____26392 with
         | (t,q) ->
             let uu____26403 = elim_delayed_subst_term t  in (uu____26403, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26423  ->
         match uu____26423 with
         | (x,q) ->
             let uu____26434 =
               let uu___212_26435 = x  in
               let uu____26436 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___212_26435.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___212_26435.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26436
               }  in
             (uu____26434, q)) bs

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
            | (uu____26520,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26526,FStar_Util.Inl t) ->
                let uu____26532 =
                  let uu____26539 =
                    let uu____26540 =
                      let uu____26553 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26553)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26540  in
                  FStar_Syntax_Syntax.mk uu____26539  in
                uu____26532 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26557 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26557 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26585 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26640 ->
                    let uu____26641 =
                      let uu____26650 =
                        let uu____26651 = FStar_Syntax_Subst.compress t4  in
                        uu____26651.FStar_Syntax_Syntax.n  in
                      (uu____26650, tc)  in
                    (match uu____26641 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26676) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26713) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26752,FStar_Util.Inl uu____26753) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26776 -> failwith "Impossible")
                 in
              (match uu____26585 with
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
          let uu____26889 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26889 with
          | (univ_names1,binders1,tc) ->
              let uu____26947 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26947)
  
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
          let uu____26990 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26990 with
          | (univ_names1,binders1,tc) ->
              let uu____27050 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27050)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27087 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27087 with
           | (univ_names1,binders1,typ1) ->
               let uu___213_27115 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_27115.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_27115.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_27115.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_27115.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___214_27136 = s  in
          let uu____27137 =
            let uu____27138 =
              let uu____27147 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27147, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27138  in
          {
            FStar_Syntax_Syntax.sigel = uu____27137;
            FStar_Syntax_Syntax.sigrng =
              (uu___214_27136.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_27136.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_27136.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_27136.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27164 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27164 with
           | (univ_names1,uu____27182,typ1) ->
               let uu___215_27196 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_27196.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_27196.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_27196.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_27196.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27202 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27202 with
           | (univ_names1,uu____27220,typ1) ->
               let uu___216_27234 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_27234.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_27234.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_27234.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___216_27234.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27268 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27268 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27293 =
                            let uu____27294 =
                              let uu____27295 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27295  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27294
                             in
                          elim_delayed_subst_term uu____27293  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___217_27298 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___217_27298.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___217_27298.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___217_27298.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___217_27298.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___218_27299 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___218_27299.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___218_27299.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___218_27299.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___218_27299.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___219_27311 = s  in
          let uu____27312 =
            let uu____27313 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27313  in
          {
            FStar_Syntax_Syntax.sigel = uu____27312;
            FStar_Syntax_Syntax.sigrng =
              (uu___219_27311.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___219_27311.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___219_27311.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___219_27311.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27317 = elim_uvars_aux_t env us [] t  in
          (match uu____27317 with
           | (us1,uu____27335,t1) ->
               let uu___220_27349 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___220_27349.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___220_27349.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___220_27349.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___220_27349.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27350 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27352 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27352 with
           | (univs1,binders,signature) ->
               let uu____27380 =
                 let uu____27389 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27389 with
                 | (univs_opening,univs2) ->
                     let uu____27416 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27416)
                  in
               (match uu____27380 with
                | (univs_opening,univs_closing) ->
                    let uu____27433 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27439 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27440 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27439, uu____27440)  in
                    (match uu____27433 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27464 =
                           match uu____27464 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27482 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27482 with
                                | (us1,t1) ->
                                    let uu____27493 =
                                      let uu____27498 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27505 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27498, uu____27505)  in
                                    (match uu____27493 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27518 =
                                           let uu____27523 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27532 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27523, uu____27532)  in
                                         (match uu____27518 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27548 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27548
                                                 in
                                              let uu____27549 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27549 with
                                               | (uu____27570,uu____27571,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27586 =
                                                       let uu____27587 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27587
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27586
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27594 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27594 with
                           | (uu____27607,uu____27608,t1) -> t1  in
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
                             | uu____27670 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27689 =
                               let uu____27690 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27690.FStar_Syntax_Syntax.n  in
                             match uu____27689 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27749 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27780 =
                               let uu____27781 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27781.FStar_Syntax_Syntax.n  in
                             match uu____27780 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27802) ->
                                 let uu____27823 = destruct_action_body body
                                    in
                                 (match uu____27823 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27868 ->
                                 let uu____27869 = destruct_action_body t  in
                                 (match uu____27869 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27918 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27918 with
                           | (action_univs,t) ->
                               let uu____27927 = destruct_action_typ_templ t
                                  in
                               (match uu____27927 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___221_27968 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___221_27968.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___221_27968.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___222_27970 = ed  in
                           let uu____27971 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27972 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27973 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27974 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27975 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27976 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27977 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27978 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27979 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27980 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27981 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27982 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27983 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27984 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___222_27970.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___222_27970.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27971;
                             FStar_Syntax_Syntax.bind_wp = uu____27972;
                             FStar_Syntax_Syntax.if_then_else = uu____27973;
                             FStar_Syntax_Syntax.ite_wp = uu____27974;
                             FStar_Syntax_Syntax.stronger = uu____27975;
                             FStar_Syntax_Syntax.close_wp = uu____27976;
                             FStar_Syntax_Syntax.assert_p = uu____27977;
                             FStar_Syntax_Syntax.assume_p = uu____27978;
                             FStar_Syntax_Syntax.null_wp = uu____27979;
                             FStar_Syntax_Syntax.trivial = uu____27980;
                             FStar_Syntax_Syntax.repr = uu____27981;
                             FStar_Syntax_Syntax.return_repr = uu____27982;
                             FStar_Syntax_Syntax.bind_repr = uu____27983;
                             FStar_Syntax_Syntax.actions = uu____27984;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___222_27970.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___223_27987 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___223_27987.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___223_27987.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___223_27987.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___223_27987.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_28006 =
            match uu___95_28006 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28033 = elim_uvars_aux_t env us [] t  in
                (match uu____28033 with
                 | (us1,uu____28057,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___224_28076 = sub_eff  in
            let uu____28077 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28080 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___224_28076.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___224_28076.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28077;
              FStar_Syntax_Syntax.lift = uu____28080
            }  in
          let uu___225_28083 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___225_28083.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___225_28083.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___225_28083.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___225_28083.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28093 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28093 with
           | (univ_names1,binders1,comp1) ->
               let uu___226_28127 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___226_28127.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___226_28127.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___226_28127.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___226_28127.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28138 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28139 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  